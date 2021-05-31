#include <math.h>
#include <stdlib.h>
#include <time.h>
#include "viterbi.h"

typedef int64_t i64;
typedef double f64;

typedef struct viterbi_model_s {
    i64 num_states;
    i64 predecessors_size;
    i64 transition_prob_size;
    i64 output_prob_size;
    struct futhark_i64_2d *predecessors;
    struct futhark_f64_2d *transition_prob;
    struct futhark_f64_1d *init_prob;
    struct futhark_f64_2d *output_prob;
} viterbi_model_t;

typedef struct viterbi_signal_s {
    i64 id_size;
    char *id;
    i64 data_size;
    struct futhark_i64_1d *data;
} viterbi_signal_t;

typedef struct instances_s {
    size_t num_signals;
    viterbi_model_t model;
    viterbi_signal_t *signals;
} instances_t;

typedef struct viterbi_result_s {
    f64 prob;
    i64 *states;
    size_t states_size;
} viterbi_result_t;

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
    i64 num_layers;
    read_i64(in, &num_layers);
    f64 *duration = (f64*) malloc(num_layers * sizeof(f64));
    for (int i = 0; i < num_layers; i++) {
        read_f64(in, &duration[i]);
    }
    i64 k;
    read_i64(in, &k);
    i64 d_max;
    read_i64(in, &d_max);
    f64 tail_factor, tail_factor_comp;
    read_f64(in, &tail_factor);
    read_f64(in, &tail_factor_comp);

    i64 states_per_layer = (i64) pow(num_bases, k);
    model->num_states = states_per_layer * num_layers;
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
    model->transition_prob_size = model->num_states * model->num_states;
    f64 *trans = (f64*) malloc(model->transition_prob_size * sizeof(f64));
    for (int i = 0; i < model->num_states; i++) {
        for (int j = 0; j < model->num_states; j++) {
            read_f64(in, &trans[i*model->num_states+j]);
        }
    }
    model->transition_prob = futhark_new_f64_2d(ctx, trans, model->num_states, model->num_states);
    free(trans);
    f64 *init = (f64*) malloc(model->num_states * sizeof(f64));
    for (int i = 0; i < model->num_states; i++) {
        if (i / states_per_layer == 0) {
            init[i] = 1.0 / states_per_layer;
        } else {
            init[i] = -(1.0 / 0.0);
        }
    }
    model->init_prob = futhark_new_f64_1d(ctx, init, model->num_states);
    model->output_prob_size = model->num_states * signal_levels;
    f64 *outp = (f64*) malloc(model->output_prob_size * sizeof(f64));
    for (int i = 0; i < model->num_states; i++) {
        for (int j = 0; j < signal_levels; j++) {
            outp[i*signal_levels+j] = observation_prob[j][i % states_per_layer];
        }
    }
    model->output_prob = futhark_new_f64_2d(ctx, outp, model->num_states, signal_levels);

    for (int i = 0; i < signal_levels; i++) {
        free(observation_prob[i]);
    }
    free(observation_prob);
    free(duration);
}

void read_signal(struct futhark_context *ctx, FILE *in, viterbi_signal_t *signal) {
    read_i64(in, &signal->id_size);
    signal->id = (char*) malloc((signal->id_size + 1) * sizeof(char));
    read_str(in, signal->id);
    read_i64(in, &signal->data_size);
    i64 *a = (i64*) malloc(signal->data_size * sizeof(i64));
    for (int i = 0; i < signal->data_size; i++) {
        read_i64(in, &a[i]);
    }
    signal->data = futhark_new_i64_1d(ctx, a, signal->data_size);
    free(a);
}

instances_t read_problem_instances(struct futhark_context *ctx, FILE *model, FILE *signals) {
    instances_t inst;
    read_model(ctx, model, &inst.model);
    read_i64(signals, &inst.num_signals);
    inst.signals = (viterbi_signal_t*) malloc(inst.num_signals * sizeof(viterbi_signal_t));
    for (int i = 0; i < inst.num_signals; i++) {
        read_signal(ctx, signals, &inst.signals[i]);
    }
    printf("Read Viterbi model and %ld signals\n", inst.num_signals);
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

void print_result_layered_model(viterbi_result_t *result) {
    print_states(result->states, result->states_size);
    printf("%lf\n", result->prob);
}

void free_model(struct futhark_context *ctx, viterbi_model_t *model) {
    futhark_free_i64_2d(ctx, model->predecessors);
    futhark_free_f64_2d(ctx, model->transition_prob);
    futhark_free_f64_1d(ctx, model->init_prob);
    futhark_free_f64_2d(ctx, model->output_prob);
}

void free_signal(struct futhark_context *ctx, viterbi_signal_t *signal) {
    futhark_free_i64_1d(ctx, signal->data);
    free(signal->id);
}

void free_result(viterbi_result_t *result) {
    free(result->states);
}

viterbi_result_t call_viterbi(struct futhark_context *ctx,
        viterbi_model_t *model, viterbi_signal_t *signal) {
    printf("Running viterbi on input signal %s\n", signal->id);
    clock_t begin = clock();
    struct futhark_opaque_v_ViterbiResult *fut_result;
    int v = futhark_entry_v_parallelViterbi(ctx, &fut_result, model->predecessors,
        model->transition_prob, model->init_prob, model->output_prob, signal->data);
    futhark_context_sync(ctx);
    if (v != 0) {
        printf("Futhark error: %s\n", futhark_context_get_error(ctx));
        exit(v);
    }

    viterbi_result_t result;
    futhark_entry_v_getProb(ctx, &result.prob, fut_result);
    result.states_size = signal->data_size;
    result.states = (i64*) malloc(result.states_size * sizeof(i64));
    struct futhark_i64_1d* states = futhark_new_i64_1d(ctx, result.states, result.states_size);
    futhark_entry_v_getStates(ctx, &states, fut_result);
    futhark_context_sync(ctx);
    futhark_values_i64_1d(ctx, states, result.states);
    futhark_free_i64_1d(ctx, states);
    futhark_free_opaque_v_ViterbiResult(ctx, fut_result);
    clock_t end = clock();
    printf("Viterbi on %s took: %lf\n", signal->id, (double)(end-begin)/CLOCKS_PER_SEC);
    return result;
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
    for (int i = 0; i < inst.num_signals; i++) {
        viterbi_result_t result = call_viterbi(ctx, &inst.model, &inst.signals[i]);
        print_result_layered_model(&result);
        free_result(&result);
        free_signal(ctx, &inst.signals[i]);
    }

    free_model(ctx, &inst.model);
    futhark_context_free(ctx);
    futhark_context_config_free(config);
    return 0;
}
