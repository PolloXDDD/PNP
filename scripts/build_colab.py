#!/usr/bin/env python3
"""Generate a self-contained single-cell Colab from the Python implementation."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
source = (ROOT / 'src/sat_eliminate.py').read_text()
source = source.split("if __name__ == '__main__':")[0]
cell = source + '''
# Upload one or several DIMACS .cnf files; download each corresponding .txt.
from google.colab import files
MAX_WIDTH = 22
MAX_CELLS = 50_000_000
TIMEOUT_SECONDS = 60.0
ORDER = 'ascending'
uploaded = files.upload()
for uploaded_name, data in uploaded.items():
    try:
        instance = parse_dimacs(data.decode('utf-8-sig'))
        answer = solve(instance, max_width=MAX_WIDTH, max_cells=MAX_CELLS,
                       timeout=TIMEOUT_SECONDS, order=ORDER)
        report = result_text(answer)
    except ResourceLimit as exc:
        report = result_text(Result('UNKNOWN', reason=str(exc)))
    except (ValueError, UnicodeError) as exc:
        report = 's ERROR\\nc ' + str(exc).replace('\\n', ' ') + '\\n'
    output_name = Path(uploaded_name).name + '.solution.txt'
    Path(output_name).write_text(report, encoding='utf-8')
    print(uploaded_name, report.splitlines()[:3])
    files.download(output_name)
'''
(ROOT / 'colab/one_cell.py').write_text(cell)
notebook = {'nbformat': 4, 'nbformat_minor': 5,
 'metadata': {'kernelspec': {'name': 'python3', 'display_name': 'Python 3'},
              'colab': {'name': 'PNP_exact_elimination.ipynb'}},
 'cells': [{'cell_type': 'code', 'id': 'exact-elimination', 'metadata': {},
            'execution_count': None, 'outputs': [], 'source': cell.splitlines(True)}]}
(ROOT / 'colab/PNP_exact_elimination.ipynb').write_text(json.dumps(notebook, indent=1) + '\n')
