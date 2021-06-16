#include <fstream>
#include <vector>

using namespace std;

vector<string> read_input(const string& file) {
    ifstream in(file);
    vector<string> v;
    string line;
    while (getline(in, line)) {
        v.emplace_back(line);
    }
    return v;
}

int levenshtein(string lhs, string rhs) {
    if (lhs.size() > rhs.size()) {
        swap(lhs, rhs);
    }
    vector<int> prev(lhs.size() + 1);
    vector<int> curr(lhs.size() + 1);
    for (int i = 0; i <= lhs.size(); i++) {
        prev[i] = i;
    }
    for (int i = 1; i <= rhs.size(); i++) {
        curr[0] = i;
        for (int j = 1; j <= lhs.size(); j++) {
            int del = prev[j] + 1;
            int ins = curr[j-1] + 1;
            int sub = prev[j-1] + (lhs[j-1] == rhs[i-1] ? 0 : 1);
            curr[j] = min(del, min(ins, sub));
        }
        swap(prev, curr);
    }
    return prev[lhs.size()];
}

double compare_strings(string lhs, string rhs) {
    int dist = levenshtein(lhs, rhs);
    return 1.0 - static_cast<double>(dist) / static_cast<double>(lhs.size());
}

int main(int argc, char** argv) {
    if (argc != 3) {
        printf("Usage: '%s <reference output> <actual output>'\n", argv[0]);
        return 1;
    }
    vector<string> lhs = read_input(argv[1]);
    vector<string> rhs = read_input(argv[2]);
    for (int i = 0; i < lhs.size(); i += 2) {
        if (lhs[i] == rhs[i]) {
            printf("%s: %lf\n", lhs[i].c_str(), compare_strings(lhs[i+1], rhs[i+1]));
        } else {
            return 1;
        }
    }
    return 0;
}
