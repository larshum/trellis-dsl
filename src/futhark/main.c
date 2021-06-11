#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "viterbi.h"

typedef int64_t i64;
typedef double f64;

typedef struct viterbi_model_s {
    i64 num_states;
    i64 num_layers;
    i64 predecessors_size;
    i64 transition_prob_size;
    i64 output_prob_size;
    i64 k;
    i64 d_max;
    i64 states_per_layer;
    f64 tail_factor;
    f64 tail_factor_comp;
    struct futhark_f64_1d *duration;
    struct futhark_i64_2d *predecessors;
    struct futhark_f64_2d *transition_prob;
    struct futhark_f64_1d *init_prob;
    struct futhark_f64_2d *output_prob;
} viterbi_model_t;

typedef struct viterbi_signals_s {
    i64 num_signals;
    i64 max_data_size;
    i64 *data_size;
    char **id;
    struct futhark_i64_2d *data;
} viterbi_signals_t;

typedef struct instances_s {
    viterbi_model_t model;
    viterbi_signals_t signals;
} instances_t;

const size_t num_bases = 4;
const char bases[] = {'A', 'C', 'G', 'T'};

void read_i64(FILE *in, i64* i) {
    if (fscanf(in, "%ld", i) != 1) {
        fprintf(stderr, "Expected i64\n");
        exit(1);
    }
}

void read_f64(FILE *in, f64* f) {
    if (fscanf(in, "%lf", f) != 1) {
        fprintf(stderr, "Expected f64\n");
        exit(1);
    }
}

void read_str(FILE *in, char* c) {
    if (fscanf(in, "%s", c) != 1) {
        fprintf(stderr, "Expected string\n");
        exit(1);
    }
}

void read_model(struct futhark_context *ctx, FILE *in, viterbi_model_t *model) {
    i64 signal_levels;
    read_i64(in, &signal_levels);
    f64** observation_prob = (f64**) malloc(signal_levels * sizeof(f64*));
    for (int i = 0; i < signal_levels; i++) {
        i64 observations;
        read_i64(in, &observations);
        observation_prob[i] = (f64*) malloc(observations * sizeof(f64));
        for (int j = 0; j < observations; j++) {
            read_f64(in, &observation_prob[i][j]);
        }
    }
    read_i64(in, &model->num_layers);
    f64 *duration = (f64*) malloc(model->num_layers * sizeof(f64));
    for (int i = 0; i < model->num_layers; i++) {
        read_f64(in, &duration[i]);
    }
    model->duration = futhark_new_f64_1d(ctx, duration, model->num_layers);
    read_i64(in, &model->k);
    read_i64(in, &model->d_max);
    read_f64(in, &model->tail_factor);
    read_f64(in, &model->tail_factor_comp);

    model->states_per_layer = (i64) pow(num_bases, model->k);
    model->num_states = model->states_per_layer * model->num_layers;
    i64 num_predecessors;
    read_i64(in, &num_predecessors);
    model->predecessors_size = model->num_states * num_predecessors;
    i64 *preds = (i64*) malloc(model->predecessors_size * sizeof(i64));
    for (int i = 0; i < model->num_states; i++) {
        for (int j = 0; j < num_predecessors; j++) {
            read_i64(in, &preds[i*num_predecessors+j]);
        }
    }
    model->predecessors = futhark_new_i64_2d(ctx, preds, model->num_states, num_predecessors);
    free(preds);
    model->transition_prob_size = 4 * model->states_per_layer;
    f64 *trans = (f64*) malloc(model->transition_prob_size * sizeof(f64));
    for (int i = 0; i < model->transition_prob_size; i++) {
        read_f64(in, &trans[i]);
    }
    model->transition_prob = futhark_new_f64_2d(ctx, trans, 4, model->states_per_layer);
    free(trans);
    f64 *init = (f64*) malloc(model->num_states * sizeof(f64));
    for (int i = 0; i < model->num_states; i++) {
        if (i / model->states_per_layer == 0) {
            init[i] = 1.0 / model->states_per_layer;
        } else {
            init[i] = -(1.0 / 0.0);
        }
    }
    model->init_prob = futhark_new_f64_1d(ctx, init, model->num_states);
    model->output_prob_size = model->num_states * signal_levels;
    f64 *outp = (f64*) malloc(model->output_prob_size * sizeof(f64));
    for (int i = 0; i < model->num_states; i++) {
        for (int j = 0; j < signal_levels; j++) {
            outp[i*signal_levels+j] = observation_prob[j][i % model->states_per_layer];
        }
    }
    model->output_prob = futhark_new_f64_2d(ctx, outp, model->num_states, signal_levels);

    for (int i = 0; i < signal_levels; i++) {
        free(observation_prob[i]);
    }
    free(observation_prob);
    free(duration);
}

void read_signals(struct futhark_context *ctx, FILE *in, viterbi_signals_t *signals) {
    read_i64(in, &signals->num_signals);
    read_i64(in, &signals->max_data_size);
    i64 *data = (i64*) malloc(signals->num_signals * signals->max_data_size * sizeof(i64));
    memset(data, 0, signals->num_signals * signals->max_data_size * sizeof(i64));
    signals->data_size = (i64*) malloc(signals->num_signals * sizeof(i64));
    signals->id = (char**) malloc(signals->num_signals * sizeof(char*));
    for (int i = 0; i < signals->num_signals; i++) {
        i64 id_len;
        read_i64(in, &id_len);
        signals->id[i] = (char*) malloc((id_len + 1) * sizeof(char));
        read_str(in, signals->id[i]);
        read_i64(in, &signals->data_size[i]);
        for (int j = 0; j < signals->data_size[i]; j++) {
            read_i64(in, &data[i*signals->max_data_size+j]);
        }
    }
    signals->data = futhark_new_i64_2d(ctx, data, signals->num_signals, signals->max_data_size);
    free(data);
}

instances_t read_problem_instances(struct futhark_context *ctx, FILE *model, FILE *signals) {
    instances_t inst;
    read_model(ctx, model, &inst.model);
    read_signals(ctx, signals, &inst.signals);
    return inst;
}

char index_to_base(int idx) {
    if (idx == 0) return 'A';
    else if (idx == 1) return 'C';
    else if (idx == 2) return 'G';
    else if (idx == 3) return 'T';
    else {
        fprintf(stderr, "Could not map index %d to a base\n", idx);
        exit(1);
    }
}

void print_states(i64 *states, size_t length) {
    for (int i = 0; i < length; i++) {
        if (states[i] < 64) {
            char last_kmer = index_to_base((states[i] >> 4) & 3);
            printf("%c", last_kmer);
        }
    }
    printf("\n");
}

void free_model(struct futhark_context *ctx, viterbi_model_t *model) {
    futhark_free_i64_2d(ctx, model->predecessors);
    futhark_free_f64_2d(ctx, model->transition_prob);
    futhark_free_f64_1d(ctx, model->init_prob);
    futhark_free_f64_2d(ctx, model->output_prob);
}

void free_signals(struct futhark_context *ctx, viterbi_signals_t *signals) {
    for (int i = 0; i < signals->num_signals; i++) {
        free(signals->id[i]);
    }
    free(signals->id);
    free(signals->data_size);
    futhark_free_i64_2d(ctx, signals->data);
}

void free_instance(struct futhark_context *ctx, instances_t *inst) {
    free_model(ctx, &inst->model);
    free_signals(ctx, &inst->signals);
}

void parallel_viterbi(struct futhark_context *ctx, instances_t *inst) {
    viterbi_model_t *model = &inst->model;
    viterbi_signals_t *signals = &inst->signals;
    printf("Running viterbi in parallel on %ld input signals\n", signals->num_signals);

    clock_t begin = clock();
    struct futhark_i64_2d *fut_result;
    int v;
    v = futhark_entry_v_parallelViterbi(ctx, &fut_result, model->predecessors,
            model->transition_prob, model->init_prob, model->output_prob,
            model->duration, model->k, model->d_max, model->states_per_layer,
            model->tail_factor, model->tail_factor_comp, signals->data);
    if (v != 0) {
        printf("Futhark error: %s\n", futhark_context_get_error(ctx));
        exit(v);
    }
    v = futhark_context_sync(ctx);
    if (v != 0) {
        printf("Futhark error: %s\n", futhark_context_get_error(ctx));
        exit(v);
    }
    clock_t end = clock();
    printf("Viterbi time: %lf\n", (double)(end-begin)/CLOCKS_PER_SEC);

    i64 *data = (i64*) malloc(signals->num_signals * signals->max_data_size * sizeof(i64));
    futhark_values_i64_2d(ctx, fut_result, data);
    futhark_free_i64_2d(ctx, fut_result);
    for (int i = 0; i < signals->num_signals; i++) {
        printf("%s\n", signals->id[i]);
        print_states(&data[i * signals->max_data_size], signals->data_size[i]);
    }
    free(data);
}

int main(int argc, char** argv) {
    if (argc != 3) {
        fprintf(stderr, "Usage: '%s <model> <signal>'\n", argv[0]);
        return 1;
    }
    FILE *model = fopen(argv[1], "r");
    FILE *signals = fopen(argv[2], "r");
    struct futhark_context_config* config = futhark_context_config_new();
    struct futhark_context* ctx = futhark_context_new(config);

    instances_t inst = read_problem_instances(ctx, model, signals);
    parallel_viterbi(ctx, &inst);

    free_instance(ctx, &inst);
    futhark_context_free(ctx);
    futhark_context_config_free(config);
    return 0;
}
