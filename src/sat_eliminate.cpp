// Exact Boolean bucket elimination. Exponential in induced width; not a P=NP proof.
// C++17, standard library only. SAT models are checked against the input clauses.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using Clock = std::chrono::steady_clock;
struct ResourceLimit : std::runtime_error { using std::runtime_error::runtime_error; };
struct Options {
  std::string input, output, order = "ascending";
  unsigned max_width = 22;
  uint64_t max_cells = 50000000, max_vars = 1000000;
  double timeout = 60.0;
};
struct Budget {
  Options options;
  Clock::time_point start = Clock::now();
  uint64_t cells = 0, steps = 0;
  size_t max_width = 0;
  explicit Budget(const Options& o) : options(o) {}
  double elapsed() const { return std::chrono::duration<double>(Clock::now() - start).count(); }
  void check() const {
    if (options.timeout > 0 && elapsed() >= options.timeout)
      throw ResourceLimit("timeout");
  }
  size_t table(size_t width) {
    check();
    max_width = std::max(max_width, width);
    if (width > options.max_width || width >= std::numeric_limits<size_t>::digits)
      throw ResourceLimit("max-width");
    const size_t count = size_t(1) << width;
    if (count > options.max_cells - cells) throw ResourceLimit("max-cells");
    cells += count;
    return count;
  }
  void tick() { if ((++steps & 4095) == 0) check(); }
};
struct Formula {
  int variables = 0;
  std::vector<std::vector<int>> original, clauses;
};
struct Factor { std::vector<int> scope; std::vector<uint8_t> values; };
struct Choice { int variable; std::vector<int> scope; std::vector<uint8_t> values; };
struct Result {
  std::string status = "UNKNOWN", reason;
  std::vector<uint8_t> model;
};

static int64_t integer(const std::string& text) {
  size_t at = 0;
  if (text.empty()) throw std::invalid_argument("empty integer");
  const int64_t value = std::stoll(text, &at);
  if (at != text.size()) throw std::invalid_argument("invalid integer: " + text);
  return value;
}

static Formula parse(std::istream& input, Budget& budget) {
  Formula f;
  std::string line;
  bool header = false, ended = false;
  uint64_t expected = 0;
  std::vector<int> clause;
  while (std::getline(input, line)) {
    budget.check();
    const auto first = line.find_first_not_of(" \t\r\n");
    if (first == std::string::npos || line[first] == 'c') continue;
    if (ended) throw std::invalid_argument("content after DIMACS % terminator");
    if (line[first] == '%') {
      if (!header || !clause.empty()) throw std::invalid_argument("misplaced % terminator");
      ended = true;
      continue;
    }
    std::istringstream row(line);
    std::string token;
    row >> token;
    if (token == "p") {
      std::string kind, n, m, extra;
      if (header || !(row >> kind >> n >> m) || kind != "cnf" || (row >> extra))
        throw std::invalid_argument("expected one strict p cnf <variables> <clauses> header");
      const int64_t nv = integer(n), nc = integer(m);
      if (nv < 0 || nc < 0 || nv > std::numeric_limits<int>::max())
        throw std::invalid_argument("invalid header range");
      if (uint64_t(nv) > budget.options.max_vars) throw ResourceLimit("max-vars");
      f.variables = int(nv); expected = uint64_t(nc); header = true;
      continue;
    }
    if (!header) throw std::invalid_argument("clause before header");
    do {
      budget.tick();
      const int64_t value = integer(token);
      if (value < -int64_t(f.variables) || value > f.variables)
        throw std::invalid_argument("literal outside declared variable range");
      if (value == 0) {
        if (f.original.size() >= expected) throw std::invalid_argument("too many clauses");
        f.original.push_back(clause);
        std::sort(clause.begin(), clause.end(), [](int a, int b) {
          const int aa = a < 0 ? -a : a, bb = b < 0 ? -b : b;
          return aa == bb ? a < b : aa < bb;
        });
        clause.erase(std::unique(clause.begin(), clause.end()), clause.end());
        bool tautology = false;
        for (size_t i = 1; i < clause.size(); ++i)
          if (clause[i] == -clause[i-1]) { tautology = true; break; }
        if (!tautology) f.clauses.push_back(clause);
        clause.clear();
      } else clause.push_back(int(value));
    } while (row >> token);
  }
  if (!header) throw std::invalid_argument("missing DIMACS header");
  if (!clause.empty()) throw std::invalid_argument("unterminated clause");
  if (f.original.size() != expected) throw std::invalid_argument("clause count differs from header");
  return f;
}

static bool verify(const Formula& f, const std::vector<uint8_t>& model) {
  if (model.size() != size_t(f.variables) + 1) return false;
  for (const auto& clause : f.original) {
    bool satisfied = false;
    for (int literal : clause) {
      const int id = literal < 0 ? -literal : literal;
      if (bool(model[id]) == (literal > 0)) { satisfied = true; break; }
    }
    if (!satisfied) return false;
  }
  return true;
}

static int choose_variable(const std::vector<Factor>& factors, const std::string& order) {
  if (order == "ascending") {
    int answer = std::numeric_limits<int>::max();
    for (const auto& f : factors) if (!f.scope.empty()) answer = std::min(answer, f.scope.front());
    return answer;
  }
  std::map<int, std::set<int>> neighbors;
  for (const auto& f : factors)
    for (int variable : f.scope)
      for (int neighbor : f.scope) if (neighbor != variable) neighbors[variable].insert(neighbor);
  // Unary factors also create candidates.
  for (const auto& f : factors) for (int variable : f.scope) neighbors[variable];
  int answer = std::numeric_limits<int>::max();
  size_t degree = std::numeric_limits<size_t>::max();
  for (const auto& entry : neighbors)
    if (entry.second.size() < degree) { answer = entry.first; degree = entry.second.size(); }
  return answer;
}

static Result solve(const Formula& formula, Budget& budget) {
  std::vector<Factor> factors;
  for (const auto& clause : formula.clauses) {
    if (clause.empty()) return {"UNSAT", "empty-clause", {}};
    Factor f;
    for (int literal : clause) f.scope.push_back(literal < 0 ? -literal : literal);
    const size_t count = budget.table(f.scope.size());
    // One falsifying row per normalized, non-tautological clause.
    f.values.assign(count, 1);
    size_t falsifying = 0;
    for (size_t i = 0; i < clause.size(); ++i)
      if (clause[i] < 0) falsifying |= size_t(1) << i;
    f.values[falsifying] = 0;
    factors.push_back(std::move(f));
  }
  std::vector<Choice> choices;
  while (!factors.empty()) {
    budget.check();
    const int variable = choose_variable(factors, budget.options.order);
    std::vector<Factor> bucket, remaining;
    std::set<int> union_set;
    for (auto& f : factors) {
      if (std::binary_search(f.scope.begin(), f.scope.end(), variable)) {
        union_set.insert(f.scope.begin(), f.scope.end());
        bucket.push_back(std::move(f));
      } else remaining.push_back(std::move(f));
    }
    factors = std::move(remaining);
    budget.table(union_set.size()); // Counts both candidate values per separator row.
    union_set.erase(variable);
    std::vector<int> separator(union_set.begin(), union_set.end());
    const size_t count = size_t(1) << separator.size();
    Factor projected{separator, std::vector<uint8_t>(count, 0)};
    Choice choice{variable, separator, std::vector<uint8_t>(count, 0)};
    std::vector<std::vector<int>> positions;
    for (const auto& f : bucket) {
      std::vector<int> pos;
      for (int id : f.scope)
        pos.push_back(id == variable ? -1 : int(std::lower_bound(separator.begin(), separator.end(), id) - separator.begin()));
      positions.push_back(std::move(pos));
    }
    bool any_true = false;
    for (size_t row = 0; row < count; ++row) {
      budget.tick();
      for (unsigned value = 0; value < 2; ++value) {
        bool feasible = true;
        for (size_t fi = 0; fi < bucket.size(); ++fi) {
          size_t index = 0;
          for (size_t bit = 0; bit < positions[fi].size(); ++bit) {
            const int pos = positions[fi][bit];
            const size_t state = pos < 0 ? value : ((row >> pos) & 1);
            index |= state << bit;
          }
          budget.tick();
          if (!bucket[fi].values[index]) { feasible = false; break; }
        }
        if (feasible) {
          projected.values[row] = 1; choice.values[row] = uint8_t(value);
          any_true = true; break;
        }
      }
    }
    if (!any_true) return {"UNSAT", "zero-projection", {}};
    choices.push_back(std::move(choice));
    if (!separator.empty()) factors.push_back(std::move(projected));
  }
  Result result{"SAT", "verified-model", std::vector<uint8_t>(size_t(formula.variables) + 1, 0)};
  for (auto it = choices.rbegin(); it != choices.rend(); ++it) {
    size_t row = 0;
    for (size_t bit = 0; bit < it->scope.size(); ++bit) row |= size_t(result.model[it->scope[bit]]) << bit;
    result.model[it->variable] = it->values[row];
  }
  budget.check();
  if (!verify(formula, result.model)) throw std::runtime_error("internal model verification failed");
  return result;
}

static Options arguments(int argc, char** argv) {
  Options o;
  for (int i = 1; i < argc; ++i) {
    const std::string arg = argv[i];
    if (arg == "--help" || arg == "-h") {
      std::cout << "Usage: sat_eliminate input.cnf [--output solution.txt] [--max-width 22]\n"
                   " [--max-cells 50000000] [--timeout 60] [--max-vars 1000000]\n"
                   " [--order ascending|min-degree]\n"
                   "Exact Boolean bucket elimination; exponential in induced width.\n"
                   "Timeout 0 disables the timer. Exit: SAT 10, UNSAT 20, UNKNOWN 0, error 2.\n";
      std::exit(0);
    }
    if (arg.rfind("--", 0) == 0) {
      if (++i == argc) throw std::invalid_argument("missing value for " + arg);
      const std::string value = argv[i];
      if (arg == "--output") o.output = value;
      else if (arg == "--order") {
        if (value != "ascending" && value != "min-degree") throw std::invalid_argument("invalid variable order");
        o.order = value;
      } else if (arg == "--timeout") {
        size_t at = 0; o.timeout = std::stod(value, &at);
        if (at != value.size() || !(o.timeout >= 0) || o.timeout > 1e12) throw std::invalid_argument("invalid timeout");
      } else {
        const int64_t n = integer(value);
        if (n < 0) throw std::invalid_argument("negative resource limit");
        if (arg == "--max-width") {
          if (n > 62) throw std::invalid_argument("max-width must be at most 62");
          o.max_width = unsigned(n);
        } else if (arg == "--max-cells") o.max_cells = uint64_t(n);
        else if (arg == "--max-vars") o.max_vars = uint64_t(n);
        else throw std::invalid_argument("unknown option " + arg);
      }
    } else {
      if (!o.input.empty()) throw std::invalid_argument("multiple input files");
      o.input = arg;
    }
  }
  if (o.input.empty()) throw std::invalid_argument("input.cnf is required; use --help");
  return o;
}

int main(int argc, char** argv) {
  try {
    const Options options = arguments(argc, argv);
    Budget budget(options);
    Result result;
    Formula formula;
    try {
      std::ifstream input(options.input);
      if (!input) throw std::invalid_argument("cannot open input file");
      formula = parse(input, budget);
      result = solve(formula, budget);
    } catch (const ResourceLimit& e) { result = {"UNKNOWN", e.what(), {}}; }
      catch (const std::bad_alloc&) { result = {"UNKNOWN", "allocation-limit", {}}; }
    std::ofstream file;
    std::ostream* out = &std::cout;
    if (!options.output.empty()) {
      file.open(options.output);
      if (!file) throw std::invalid_argument("cannot open output file");
      out = &file;
    }
    *out << "c algorithm boolean-bucket-elimination\n"
         << "c complexity exponential-in-induced-width\n"
         << "c order " << options.order << '\n'
         << "c reason " << result.reason << '\n'
         << "c max_width " << budget.max_width << '\n'
         << "c cells " << budget.cells << '\n'
         << "c elapsed_seconds " << std::fixed << std::setprecision(6) << budget.elapsed() << '\n';
    *out << "s " << (result.status == "SAT" ? "SATISFIABLE" : result.status == "UNSAT" ? "UNSATISFIABLE" : "UNKNOWN") << '\n';
    if (result.status == "SAT") {
      *out << "v";
      for (int id = 1; id <= formula.variables; ++id) {
        if (id > 1 && (id - 1) % 32 == 0) *out << " 0\nv";
        *out << ' ' << (result.model[id] ? id : -id);
      }
      *out << " 0\n";
    }
    out->flush();
    if (!*out) throw std::runtime_error("failed to write result");
    return result.status == "SAT" ? 10 : result.status == "UNSAT" ? 20 : 0;
  } catch (const std::exception& e) {
    std::cerr << "error: " << e.what() << '\n';
    return 2;
  }
}
