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


def plot_coverage_values(file_paths: list[str]) -> None:
    num_files = []
    lines_coverage = []
    functions_coverage = []
    branches_coverage = []
    file_paths = sorted(file_paths)
    logger.debug(f'File paths sorted: {file_paths}')

    for file_path in file_paths:
        num_file = int(file_path.split('/')[-2].split('_')[0])
        num_files.append(num_file)

        coverage_values = extract_coverage_values(file_path)
        lines_coverage.append(coverage_values['Lines'])
        functions_coverage.append(coverage_values['Functions'])
        branches_coverage.append(coverage_values['Branches'])

    plt.xkcd()

    _, ax = plt.subplots()
    ax.plot(num_files, lines_coverage, label='Lines', marker='o')
    ax.plot(num_files, functions_coverage, label='Functions', marker='s')
    ax.plot(num_files, branches_coverage, label='Branches', marker='^')

    ax.set_xlabel('Number of Files')
    ax.set_ylabel('Coverage (%)')
    ax.set_title('Coverage vs. Number of Files')

    ax.legend()

    plt.show()


def find_coverage_reports(directory: str) -> list[str]:
    pattern = os.path.join(directory, '*_files', 'coverage_report.html')
    return glob.glob(pattern)


directory = './coverage_reports.bak'

file_paths = find_coverage_reports(directory)
logger.debug(f'Found {len(file_paths)} coverage report files.')
logger.debug(file_paths)

plot_coverage_values(file_paths)
