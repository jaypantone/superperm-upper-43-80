#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <random>
#include <set>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
#include <sstream>

// Literal coverage and exhaustive single-deletion checking. No construction
// certificate is read. One byte per permutation count, with exact overflow
// counts in a sparse map. The deletion pass merges forbidden intervals with
// constant auxiliary storage (besides its output list).
using Rank = int64_t;
using Word = std::vector<uint8_t>;
static_assert(sizeof(size_t) >= 8, "This checker requires a 64-bit platform.");

struct Checker {
    int n;
    const Word& word;
    std::array<uint64_t, 14> fact{};
    std::vector<uint8_t> count;
    std::unordered_map<uint64_t, uint64_t> overflow;
    uint64_t distinct = 0, occurrences = 0;

    Checker(int degree, const Word& w) : n(degree), word(w) {
        if (n < 2 || n > 13) throw std::runtime_error("degree must be 2..13");
        fact[0] = 1;
        for (int i = 1; i <= n; ++i) fact[i] = i * fact[i-1];
        count.resize(fact[n]);
        for (size_t start = 0; start + n <= word.size(); ++start) {
            auto rank = window_rank(start);
            if (rank < 0) continue;
            auto& c = count[rank];
            if (c == 0) ++distinct;
            if (c < 255) ++c;
            else ++overflow[rank];
            ++occurrences;
        }
    }

    Rank window_rank(size_t start, size_t skip = SIZE_MAX) const {
        unsigned unused = (1u << n) - 1;
        uint64_t value = 0;
        for (int j = 0; j < n; ++j) {
            auto pos = start + j;
            if (pos >= skip) ++pos;
            unsigned bit = 1u << word[pos];
            if (!(unused & bit)) return -1;
            value += __builtin_popcount(unused & (bit-1)) * fact[n-j-1];
            unused ^= bit;
        }
        return Rank(value);
    }

    std::vector<size_t> reference_deletions() const {
        std::array<Rank, 13> ring{}, needed{};
        ring.fill(-1);
        std::vector<size_t> answer;
        const size_t length = word.size();
        const size_t windows = length >= size_t(n) ? length-n+1 : 0;
        for (size_t k = 0; k < length; ++k) {
            if (k < windows) ring[k % n] = window_rank(k);
            auto first = k >= size_t(n-1) ? k-n+1 : 0;
            auto stop = std::min(k+1, windows);
            int missing = 0;
            // A permutation cannot repeat at distance less than n: that would
            // repeat a letter inside it. Consequently all destroyed valid
            // windows have distinct ranks, and only globally unique ones need
            // replacing. A byte count is sufficient for this exact predicate.
            for (size_t s = first; s < stop; ++s) {
                auto rank = ring[s % n];
                if (rank >= 0 && count[rank] == 1) needed[missing++] = rank;
            }
            // New starts cross the deletion seam; windows wholly to either
            // side persist unchanged, including the boundary cases.
            auto new_stop = windows ? std::min(k, windows-1) : 0;
            auto new_count = new_stop > first ? new_stop-first : 0;
            if (size_t(missing) > new_count) continue;
            for (size_t s = first; missing && s < new_stop; ++s) {
                auto rank = window_rank(s, k);
                for (int i = 0; i < missing; ++i) {
                    if (needed[i] == rank) { needed[i] = needed[--missing]; break; }
                }
            }
            if (!missing) answer.push_back(k);
        }
        return answer;
    }

    std::vector<size_t> deletions() const {
        std::vector<size_t> answer;
        size_t covered_end = 0;
        // Two equal permutation windows cannot start less than n positions
        // apart, so one deletion cannot destroy both occurrences. Only unique
        // windows impose restrictions. Deleting an interior letter of a unique
        // permutation cannot recreate it across the seam: the overlapping old
        // and new copies would repeat a symbol within that permutation.
        // Deleting its first or last letter can recreate it only when the
        // adjacent exterior letter is equal. Thus each unique window forbids
        // precisely the interval below. Starts are ordered, so a streaming
        // interval union computes all permissible positions exactly.
        for (size_t s = 0; s+n <= word.size(); ++s) {
            auto rank = window_rank(s);
            if (rank < 0 || count[rank] != 1) continue;
            size_t first = s + (s > 0 && word[s-1] == word[s]);
            size_t stop = s+n - (s+n < word.size() && word[s+n-1] == word[s+n]);
            if (first >= stop) continue;
            while (covered_end < first) answer.push_back(covered_end++);
            covered_end = std::max(covered_end,stop);
        }
        while (covered_end < word.size()) answer.push_back(covered_end++);
        return answer;
    }
};

static std::set<Word> naive(int n, const Word& word) {
    std::set<Word> seen;
    for (size_t i = 0; i+n <= word.size(); ++i) {
        Word p(word.begin()+i, word.begin()+i+n), sorted = p;
        std::sort(sorted.begin(), sorted.end());
        bool valid = true;
        for (int j = 0; j < n; ++j) if (sorted[j] != j) valid = false;
        if (valid) seen.insert(p);
    }
    return seen;
}

static uint64_t controls() {
    uint64_t cases = 0;
    auto test = [&](int n, const Word& w) {
        Checker c(n, w);
        auto before = naive(n, w);
        if (c.distinct != before.size()) throw std::runtime_error("coverage control failed");
        std::vector<size_t> expected;
        for (size_t k = 0; k < w.size(); ++k) {
            auto next = w; next.erase(next.begin()+k);
            auto after = naive(n, next);
            if (std::includes(after.begin(), after.end(), before.begin(), before.end())) expected.push_back(k);
        }
        if (expected != c.deletions()) throw std::runtime_error("deletion control failed");
        if (expected != c.reference_deletions()) throw std::runtime_error("reference deletion control failed");
        ++cases;
    };
    for (int n : {2,3}) {
        uint64_t limit = 1;
        for (int length = 0; length <= 8; ++length, limit *= n) {
            for (uint64_t code = 0; code < limit; ++code) {
                Word w(length); auto q = code;
                for (auto& x : w) { x = q%n; q /= n; }
                test(n,w);
            }
        }
    }
    std::mt19937 rng(20260912);
    for (int n : {4,5,6,7}) for (int t = 0; t < 100; ++t) {
        Word w;
        for (int j = 0; j < 8; ++j) {
            Word p(n); for (int i = 0; i < n; ++i) p[i] = i;
            std::shuffle(p.begin(), p.end(), rng);
            w.insert(w.end(), p.begin(), p.end());
            if (j%2 == 0) w.push_back(p.back());
        }
        test(n,w);
    }
    for (int n = 2; n <= 9; ++n) {
        Word p(n); for (int i = 0; i < n; ++i) p[i] = i;
        Checker c(n,p); uint64_t expected = 0;
        do { if (c.window_rank(0) != Rank(expected++)) throw std::runtime_error("rank control failed"); }
        while (std::next_permutation(p.begin(), p.end()));
        if (expected != c.fact[n]) throw std::runtime_error("rank range failed");
    }
    // Exercise exact multiplicities after the byte counter saturates.
    Word repeated; for (int i = 0; i < 300; ++i) { repeated.push_back(0); repeated.push_back(1); }
    Checker c(2,repeated);
    if (c.occurrences != 599 || c.overflow.at(0) != 45 || c.overflow.at(1) != 44)
        throw std::runtime_error("overflow control failed");
    return cases;
}

int main(int argc, char** argv) {
    try {
        if (argc == 2 && std::string(argv[1]) == "--self-test") {
            std::cout << "{\"passed\":true,\"brute_force_word_controls\":" << controls()
                      << ",\"exhaustive_rank_degrees\":[2,3,4,5,6,7,8,9]}\n"; return 0;
        }
        if (argc < 4 || argc > 5) throw std::runtime_error("usage: literal_check N ALPHABET WORD.txt [--deletions]");
        size_t parsed = 0;
        int n = std::stoi(argv[1], &parsed);
        if (parsed != std::string(argv[1]).size()) throw std::runtime_error("invalid degree");
        if (n < 2 || n > 13) throw std::runtime_error("degree must be 2..13");
        const std::string alphabet = argv[2];
        if (alphabet.size() != size_t(n)) throw std::runtime_error("alphabet length must equal degree");
        auto sorted_alphabet = alphabet; std::sort(sorted_alphabet.begin(), sorted_alphabet.end());
        if (std::adjacent_find(sorted_alphabet.begin(), sorted_alphabet.end()) != sorted_alphabet.end())
            throw std::runtime_error("alphabet symbols must be distinct");
        for (uint8_t c : alphabet) if (c < 33 || c > 126 || c == '"' || c == '\\')
            throw std::runtime_error("alphabet requires printable ASCII excluding quote/backslash/whitespace");
        bool deletion_scan = argc == 5;
        if (deletion_scan && std::string(argv[4]) != "--deletions") throw std::runtime_error("unknown option");
        auto begin = std::chrono::steady_clock::now();
        std::ifstream input(argv[3], std::ios::binary | std::ios::ate);
        if (!input) throw std::runtime_error("cannot open input");
        auto length = input.tellg(); if (length < 0) throw std::runtime_error("cannot determine length");
        Word word(static_cast<size_t>(length)); input.seekg(0);
        input.read(reinterpret_cast<char*>(word.data()), word.size());
        if (!input) throw std::runtime_error("input read failed");
        bool final_lf = !word.empty() && word.back() == '\n';
        if (final_lf) word.pop_back();
        std::array<int, 256> decode; decode.fill(-1);
        for (int j = 0; j < n; ++j) decode[uint8_t(alphabet[j])] = j;
        for (auto& c : word) { if (decode[c] < 0) throw std::runtime_error("invalid input symbol"); c = decode[c]; }
        auto loaded = std::chrono::steady_clock::now();
        Checker check(n,word);
        auto scanned = std::chrono::steady_clock::now();
        std::ostringstream report;
        report << "{\"n\":" << n << ",\"alphabet\":\"" << alphabet.substr(0,n)
                  << "\",\"normalization\":\"discard exactly one optional final LF\",\"final_lf_present\":"
                  << (final_lf ? "true" : "false") << ",\"length\":" << word.size()
                  << ",\"permutation_occurrences\":" << check.occurrences << ",\"distinct_permutations\":" << check.distinct
                  << ",\"required_permutations\":" << check.fact[n] << ",\"missing_permutations\":" << check.fact[n]-check.distinct
                  << ",\"extra_occurrences\":" << check.occurrences-check.distinct
                  << ",\"load_seconds\":" << std::chrono::duration<double>(loaded-begin).count()
                  << ",\"scan_seconds\":" << std::chrono::duration<double>(scanned-loaded).count();
        if (deletion_scan) {
            if (check.distinct != check.fact[n]) throw std::runtime_error("deletion scan requires full coverage");
            auto answer = check.deletions();
            auto finished = std::chrono::steady_clock::now();
            report << ",\"tested_deletions\":" << word.size() << ",\"coverage_preserving_deletions\":[";
            for (size_t j = 0; j < answer.size(); ++j) { if (j) report << ','; report << answer[j]; }
            report << "],\"deletion_seconds\":" << std::chrono::duration<double>(finished-scanned).count();
        }
        report << "}\n"; std::cout << report.str();
        return check.distinct == check.fact[n] ? 0 : 3;
    } catch (const std::exception& e) { std::cerr << e.what() << '\n'; return 2; }
}
