import glob
import logging
import os
from typing import TYPE_CHECKING

import matplotlib.pyplot as plt
from bs4 import BeautifulSoup, ResultSet
from bs4.element import Tag

logging.basicConfig(level=logging.INFO, format='%(levelname)s - %(message)s')
logger = logging.getLogger(__name__)


def extract_coverage_values(file_path: str) -> dict[str, float]:
    with open(file_path, 'r', encoding='utf-8') as file:
        html_content = file.read()

    soup = BeautifulSoup(html_content, 'html.parser')

    coverage_values: dict[str, float] = {}

    coverage_table = soup.find('table', class_='coverage')

    if coverage_table and isinstance(coverage_table, Tag):
        rows = coverage_table.find_all('tr')

        extract_coverage_data(coverage_values, rows)

    return coverage_values


def extract_coverage_data(coverage_values: dict[str, float], rows: ResultSet[Tag]) -> None:
    for row in rows:
        cells = row.find_all('th')
        if cells:
            if is_first_line(cells):
                continue
            first_cell = cells[0]
            if TYPE_CHECKING:
                assert isinstance(first_cell, Tag)
            label, value = extract_coverage_label_value(row, first_cell)
            coverage_values[label] = value


def extract_coverage_label_value(row: Tag, first_cell: Tag) -> tuple[str, float]:
    label = first_cell.text.strip(':')
    value_cell = row.find_all('td')[2]
    if TYPE_CHECKING:
        assert isinstance(value_cell, Tag)
    value = float(value_cell.text.strip('%'))
    return label, value


def is_first_line(cells: list[Tag]) -> bool:
    return len(cells) == 4 and cells[1].text == 'Exec'


def plot_coverage_values(file_paths: list[str], *, is_synced: bool = False) -> None:
    file_indices = []
    lines_coverage = []
    functions_coverage = []
    branches_coverage = []
    file_paths = sorted(file_paths)
    logger.debug(f'File paths sorted: {file_paths}')

    for file_path in file_paths:
        if is_synced:
            file_index = file_path.split('/')[-2].split('_')[0]
        else:
            file_index = file_path.split('/')[-2]

        coverage_values = extract_coverage_values(file_path)
        # Skip entries where all coverage values are 0
        if coverage_values['Lines'] == 0 and coverage_values['Functions'] == 0 and coverage_values['Branches'] == 0:
            logger.debug(f'Skipping {file_index} because all coverage values are 0')
            continue

        file_indices.append(file_index)
        lines_coverage.append(coverage_values['Lines'])
        functions_coverage.append(coverage_values['Functions'])
        branches_coverage.append(coverage_values['Branches'])

    # Sort all data based on lines_coverage
    sorted_data = sorted(zip(lines_coverage, functions_coverage, branches_coverage, file_indices, strict=False))
    lines_coverage, functions_coverage, branches_coverage, file_indices = zip(*sorted_data, strict=False)  # type: ignore[assignment]

    plt.xkcd()

    _, ax = plt.subplots()

    ax.axhline(y=37.3, color='red', linestyle='--', label='Transfuzz Line Coverage')
    ax.axhline(y=39.3, color='red', linestyle=':', label='Verismith Line Coverage')

    ax.plot(range(len(file_indices)), lines_coverage, label='Line coverage', marker='o')
    ax.plot(range(len(file_indices)), functions_coverage, label='Function coverage', marker='s')
    ax.plot(range(len(file_indices)), branches_coverage, label='Branch coverage', marker='^')

    # Set diagonal labels for x-axis
    # ax.set_xticks(range(len(file_indices)))
    # ax.set_xticklabels(file_indices, rotation=65, ha='right')

    ax.set_ylabel('Coverage (%)')
    if is_synced:
        ax.set_title('Coverage vs. Number of Files')
        ax.set_xlabel('Number of Files')
    else:
        ax.set_title('Coverage progression vs. Generated snippets')
        ax.set_xlabel('Test files generated')

    ax.legend(loc='upper left', bbox_to_anchor=(0, 1), fontsize='small')

    # Add tight_layout to ensure the rotated labels fit
    plt.tight_layout()

    plt.show()


def find_coverage_reports(
    directory: str,
    *,
    is_verismith: bool = False,
    is_transfuzz: bool = False,
    is_comparison: bool = False,
    is_perso: bool = False,
) -> list[str]:
    if is_verismith:
        pattern = os.path.join(directory, 'verismith-synced', '*_files', 'coverage_report.html')
    elif is_transfuzz:
        pattern = os.path.join(directory, 'transfuzz-synced', '*_files', 'coverage_report.html')
    elif is_comparison:
        pattern = os.path.join(directory, 'comparison', '*', 'coverage_report.html')
    elif is_perso:
        pattern = os.path.join(directory, 'perso', '*', 'coverage_report.html')
    else:
        raise ValueError('At least one of is_verismith, is_transfuzz, is_comparison, or is_perso must be True.')
    return glob.glob(pattern)


if __name__ == '__main__':
    directory = './coverage_reports.bak/verilator'
    is_verismith = False
    is_transfuzz = False
    is_comparison = False
    is_perso = True
    assert 1 == sum(
        1 if i is True else 0 for i in [is_verismith, is_transfuzz, is_comparison, is_perso]
    ), 'Only one of is_verismith, is_transfuzz, or is_comparison can be True.'
    file_paths = find_coverage_reports(
        directory,
        is_verismith=is_verismith,
        is_transfuzz=is_transfuzz,
        is_comparison=is_comparison,
        is_perso=is_perso,
    )
    logger.debug(f'Found {len(file_paths)} coverage report files.')
    logger.debug(file_paths)

    plot_coverage_values(file_paths, is_synced=is_verismith or is_transfuzz)
