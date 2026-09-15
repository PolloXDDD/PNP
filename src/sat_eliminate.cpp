// Exact Boolean bucket elimination. General worst-case cost is exponential.
// C++17, standard library only. Witnesses are checked against the input CNF.
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <queue>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
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
  uint64_t cells = 0, ticks = 0, rows = 0, eliminated = 0;
  size_t max_width = 0;
  explicit Budget(const Options& o) : options(o) {}
  double elapsed() const { return std::chrono::duration<double>(Clock::now() - start).count(); }
  void check() const {
    if (elapsed() >= options.timeout) throw ResourceLimit("time budget exceeded");
  }
  void observe_width(size_t width) {
    max_width = std::max(max_width, width);
    if (width > options.max_width) throw ResourceLimit("scope width exceeds limit");
  }
  size_t table(size_t width, uint64_t copies = 1) {
    check();
    observe_width(width);
    if (width >= std::numeric_limits<size_t>::digits)
      throw ResourceLimit("table exceeds addressable size");
    const size_t count = size_t(1) << width;
    if (count > (options.max_cells - cells) / copies)
      throw ResourceLimit("cumulative table cell budget exceeded");
    cells += copies * count;
    return count;
  }
  void tick() { if ((++ticks & 1023U) == 0) check(); }
};
struct Formula {
  int variables = 0;
  std::vector<std::vector<int>> original;
};
struct Factor { std::vector<int> scope; std::vector<uint8_t> values; };
struct Choice { int variable; std::vector<int> scope; std::vector<uint8_t> values; };
struct Result {
  std::string status = "UNKNOWN", reason;
  std::vector<uint8_t> model;
};

static int64_t integer(const std::string& text) {
  size_t start = (!text.empty() && (text[0] == '-' || text[0] == '+')) ? 1U : 0U;
  if (start == text.size()) throw std::invalid_argument("invalid integer: " + text);
  for (size_t i = start; i < text.size(); ++i)
    if (text[i] < '0' || text[i] > '9') throw std::invalid_argument("invalid integer: " + text);
  size_t at = 0;
  const int64_t value = std::stoll(text, &at);
  if (at != text.size()) throw std::invalid_argument("invalid integer: " + text);
  return value;
}

// Parsing and output are deliberately outside the solving timer.
static Formula parse(std::istream& input, const Options& options) {
  Formula f;
  std::string line;
  bool header = false, first_line = true;
  uint64_t expected = 0;
  std::vector<int> clause;
  while (std::getline(input, line)) {
    if (first_line && line.compare(0, 3, "\xef\xbb\xbf") == 0) line.erase(0, 3);
    first_line = false;
    const auto first = line.find_first_not_of(" \t\r\n");
    if (first == std::string::npos || line[first] == 'c') continue;
    std::istringstream row(line);
    std::string token;
    row >> token;
    // The conventional percent end marker ignores the remainder of the stream.
    // Completeness is still checked below (including an unfinished clause).
    if (!token.empty() && token.front() == '%') break;
    if (token == "p") {
      std::string kind, n, m, extra;
      if (header || !(row >> kind >> n >> m) || kind != "cnf" || (row >> extra))
        throw std::invalid_argument("expected one strict p cnf <variables> <clauses> header");
      const int64_t nv = integer(n), nc = integer(m);
      if (nv < 0 || nc < 0 || nv > std::numeric_limits<int>::max())
        throw std::invalid_argument("invalid header range");
      if (uint64_t(nv) > options.max_vars) throw ResourceLimit("declared variables exceed limit");
      f.variables = int(nv); expected = uint64_t(nc); header = true;
      continue;
    }
    if (!header) throw std::invalid_argument("clause before header");
    do {
      const int64_t value = integer(token);
      if (value < -int64_t(f.variables) || value > f.variables)
        throw std::invalid_argument("literal outside declared variable range");
      if (value == 0) {
        if (f.original.size() >= expected) throw std::invalid_argument("too many clauses");
        f.original.push_back(clause);
        clause.clear();
      } else clause.push_back(int(value));
    } while (row >> token);
  }
  if (input.bad()) throw std::invalid_argument("failed to read input file");
  if (!header) throw std::invalid_argument("missing DIMACS header");
  if (!clause.empty()) throw std::invalid_argument("unterminated clause");
  if (f.original.size() != expected) throw std::invalid_argument("clause count differs from header");
  return f;
}

static bool verify(const Formula& f, const std::vector<uint8_t>& model, Budget& budget) {
  if (model.size() != size_t(f.variables) + 1) return false;
  for (const auto& clause : f.original) {
    bool satisfied = false;
    for (int literal : clause) {
      budget.tick();
      const int id = literal < 0 ? -literal : literal;
      if (bool(model[id]) == (literal > 0)) { satisfied = true; break; }
    }
    if (!satisfied) return false;
  }
  return true;
}

// Exact primal-graph degree maintenance. An elimination completes the separator
// to a clique, removes its pivot, and refreshes only affected heap entries.
class DegreeOrder {
  using Entry = std::pair<size_t, int>;
  std::map<int, std::set<int>> neighbors;
  std::priority_queue<Entry, std::vector<Entry>, std::greater<Entry>> heap;
 public:
  void add_initial_scope(const std::vector<int>& scope, Budget& budget) {
    for (int v : scope) {
      auto& adjacent = neighbors[v];
      for (int u : scope) { budget.tick(); if (u != v) adjacent.insert(u); }
    }
  }
  void initialize() { for (const auto& e : neighbors) heap.emplace(e.second.size(), e.first); }
  int choose() {
    while (!heap.empty()) {
      const auto entry = heap.top();
      heap.pop();
      const auto it = neighbors.find(entry.second);
      if (it != neighbors.end() && it->second.size() == entry.first) return entry.second;
    }
    throw std::logic_error("empty variable-order heap");
  }
  void eliminate(int pivot, const std::vector<int>& separator, Budget& budget) {
    for (int v : separator) {
      auto& adjacent = neighbors.at(v);
      adjacent.erase(pivot);
      for (int u : separator) { budget.tick(); if (u != v) adjacent.insert(u); }
      heap.emplace(adjacent.size(), v);
    }
    neighbors.erase(pivot);
  }
};

static Result solve(const Formula& formula, Budget& budget) {
  std::map<size_t, Factor> factors;
  std::map<int, std::set<size_t>> buckets;
  size_t serial = 0;
  DegreeOrder degree;
  auto add = [&](Factor factor) {
    const size_t id = serial++;
    for (int variable : factor.scope) { budget.tick(); buckets[variable].insert(id); }
    factors.emplace(id, std::move(factor));
  };
  // A syntactic empty clause needs no table allocation or search.
  for (const auto& clause : formula.original)
    if (clause.empty()) return {"UNSAT", "empty-clause", {}};
  for (const auto& original : formula.original) {
    budget.check();
    auto clause = original;
    std::sort(clause.begin(), clause.end(), [](int a, int b) {
      const int aa = a < 0 ? -a : a, bb = b < 0 ? -b : b;
      return aa == bb ? a < b : aa < bb;
    });
    clause.erase(std::unique(clause.begin(), clause.end()), clause.end());
    bool tautology = false;
    for (size_t i = 1; i < clause.size(); ++i)
      if (clause[i] == -clause[i-1]) { tautology = true; break; }
    if (tautology) continue;
    Factor f;
    for (int literal : clause) f.scope.push_back(literal < 0 ? -literal : literal);
    const size_t count = budget.table(f.scope.size());
    f.values.assign(count, 1);
    size_t falsifying = 0;
    for (size_t i = 0; i < clause.size(); ++i)
      if (clause[i] < 0) falsifying |= size_t(1) << i;
    f.values[falsifying] = 0;
    if (budget.options.order == "min-degree") degree.add_initial_scope(f.scope, budget);
    add(std::move(f));
  }
  if (budget.options.order == "min-degree") degree.initialize();
  std::vector<Choice> choices;
  while (!buckets.empty()) {
    budget.check();
    const int variable = budget.options.order == "ascending" ? buckets.begin()->first : degree.choose();
    const auto ids = buckets.at(variable);
    std::vector<const Factor*> selected;
    std::set<int> union_set;
    for (size_t id : ids) {
      budget.tick();
      const auto& f = factors.at(id);
      union_set.insert(f.scope.begin(), f.scope.end());
      selected.push_back(&f);
    }
    budget.observe_width(union_set.size());
    union_set.erase(variable);
    std::vector<int> separator(union_set.begin(), union_set.end());
    const size_t count = budget.table(separator.size(), 2);
    Factor projected{separator, std::vector<uint8_t>(count, 0)};
    Choice choice{variable, separator, std::vector<uint8_t>(count, 0)};
    struct Plan {
      const std::vector<uint8_t>* table;
      std::vector<std::pair<size_t, size_t>> mapping;
      size_t pivot;
    };
    std::vector<Plan> plans;
    for (const Factor* f : selected) {
      Plan plan{&f->values, {}, 0};
      for (size_t bit = 0; bit < f->scope.size(); ++bit) {
        const int id = f->scope[bit];
        if (id == variable) plan.pivot = size_t(1) << bit;
        else plan.mapping.emplace_back(size_t(std::lower_bound(separator.begin(), separator.end(), id) - separator.begin()), bit);
      }
      plans.push_back(std::move(plan));
    }
    bool any_true = false;
    for (size_t row = 0; row < count; ++row) {
      budget.tick();
      bool ok0 = true, ok1 = true;
      for (const auto& plan : plans) {
        size_t index = 0;
        for (const auto& bit : plan.mapping) index |= ((row >> bit.first) & 1U) << bit.second;
        ok0 = ok0 && (*plan.table)[index];
        ok1 = ok1 && (*plan.table)[index | plan.pivot];
        budget.tick();
        if (!ok0 && !ok1) break;
      }
      if (ok0 || ok1) {
        projected.values[row] = 1; choice.values[row] = uint8_t(ok0 ? 0 : 1);
        any_true = true;
      }
    }
    budget.rows += count;
    if (!any_true) return {"UNSAT", "zero-projection", {}};
    choices.push_back(std::move(choice));
    for (size_t id : ids) {
      const auto& f = factors.at(id);
      for (int v : f.scope) { budget.tick(); buckets.at(v).erase(id); }
      factors.erase(id);
    }
    buckets.erase(variable);
    // Retain true scopes so the induced-width calculation is reproducible.
    if (!separator.empty()) add(std::move(projected));
    if (budget.options.order == "min-degree") degree.eliminate(variable, separator, budget);
    ++budget.eliminated;
  }
  Result result{"SAT", "verified-model", std::vector<uint8_t>(size_t(formula.variables) + 1, 0)};
  for (auto it = choices.rbegin(); it != choices.rend(); ++it) {
    budget.tick();
    size_t row = 0;
    for (size_t bit = 0; bit < it->scope.size(); ++bit) row |= size_t(result.model[it->scope[bit]]) << bit;
    result.model[it->variable] = it->values[row];
  }
  budget.check();
  if (!verify(formula, result.model, budget)) throw std::runtime_error("internal model verification failed");
  budget.check();
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
                   "Timeout 0 gives zero search budget. Parsing and output are excluded.\n"
                   "Exit: SAT 10, UNSAT 20, UNKNOWN 0, error 2.\n";
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
        if (at != value.size() || !std::isfinite(o.timeout) || o.timeout < 0)
          throw std::invalid_argument("invalid timeout");
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
    double elapsed = 0.0;
    try {
      std::ifstream input(options.input);
      if (!input) throw std::invalid_argument("cannot open input file");
      formula = parse(input, options);
      budget.start = Clock::now();
      try { result = solve(formula, budget); }
      catch (const ResourceLimit& e) { result = {"UNKNOWN", e.what(), {}}; }
      catch (const std::bad_alloc&) { result = {"UNKNOWN", "memory allocation failed", {}}; }
      elapsed = budget.elapsed();
    } catch (const ResourceLimit& e) { result = {"UNKNOWN", e.what(), {}}; }
      catch (const std::bad_alloc&) { result = {"UNKNOWN", "memory allocation failed during input", {}}; }
    std::ofstream file;
    std::ostream* out = &std::cout;
    if (!options.output.empty()) {
      file.open(options.output);
      if (!file) throw std::invalid_argument("cannot open output file");
      out = &file;
    }
    *out << "c Exact Boolean bucket elimination; general cost is exponential\n"
         << "c reason " << result.reason << '\n';
    *out << "s " << (result.status == "SAT" ? "SATISFIABLE" : result.status == "UNSAT" ? "UNSATISFIABLE" : "UNKNOWN") << '\n';
    if (result.status == "SAT") {
      *out << "v";
      for (int id = 1; id <= formula.variables; ++id) {
        if (id > 1 && (id - 1) % 20 == 0) *out << "\nv";
        *out << ' ' << (result.model[id] ? id : -id);
      }
      *out << " 0\n";
    }
    *out << "c stats {\"nvars\":" << formula.variables
         << ",\"clauses\":" << formula.original.size()
         << ",\"order\":\"" << options.order << "\",\"max_width\":" << budget.max_width
         << ",\"cells\":" << budget.cells << ",\"rows\":" << budget.rows
         << ",\"eliminated\":" << budget.eliminated
         << ",\"elapsed_seconds\":" << std::fixed << std::setprecision(9) << elapsed << "}\n";
    out->flush();
    if (!*out) throw std::runtime_error("failed to write result");
    return result.status == "SAT" ? 10 : result.status == "UNSAT" ? 20 : 0;
  } catch (const std::exception& e) {
    std::cerr << "error: " << e.what() << '\n';
    return 2;
  }
}
