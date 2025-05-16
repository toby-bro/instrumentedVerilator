import argparse
import json
import logging
from typing import List, Tuple

logging.basicConfig(level=logging.INFO, format='%(levelname)s - %(message)s')
logger = logging.getLogger(__name__)


def find_low_coverage_from_json(
    json_file_path: str,
    threshold: float,
    min_threshold: float = 0.0,
) -> List[Tuple[str, float]]:
    """
    Parses a fastcov coverage.json file to find files within a coverage range.

    Args:
        json_file_path: Path to the fastcov coverage.json file.
        threshold: The upper coverage percentage threshold (0-100).
                   Files with coverage < threshold are considered.
        min_threshold: The lower coverage percentage threshold (0-100).
                       Files with coverage >= min_threshold are considered.
                       Default is 0.0.

    Returns:
        A list of tuples (source_file_name, coverage_percentage),
        sorted by percentage, for files where min_threshold <= coverage < threshold.
    """
    coverage_results: List[Tuple[str, float]] = []

    try:
        with open(json_file_path, 'r', encoding='utf-8') as f:
            coverage_data = json.load(f)
    except FileNotFoundError:
        logger.error(f'Fastcov JSON file not found: {json_file_path}')
        return []
    except json.JSONDecodeError:
        logger.error(f'Error decoding JSON from file: {json_file_path}')
        return []
    except Exception as e:
        logger.error(f'Error reading fastcov JSON file {json_file_path}: {e}')
        return []

    assert isinstance(coverage_data, dict), f'Invalid JSON format in {json_file_path}'
    assert 'sources' in coverage_data, f'Invalid JSON format in {json_file_path}'
    assert isinstance(coverage_data['sources'], dict), f'Invalid JSON format in {json_file_path}'

    logger.debug(f"Processing coverage data from '{json_file_path}'...")
    for source_file_name, _file_info in coverage_data['sources'].items():
        assert isinstance(_file_info, dict), f'Invalid JSON format in {json_file_path}'
        file_info = _file_info['']
        if not isinstance(file_info, dict):
            logger.warning(f'Skipping invalid file info: {file_info}')
            continue

        lines_info = file_info.get('lines')

        assert isinstance(lines_info, dict), f'Invalid JSON format in {json_file_path}'

        coverage_percentage = len([cov for cov in lines_info.values() if cov > 0]) / len(lines_info) * 100.0

        coverage_results.append((source_file_name, float(coverage_percentage)))

    logger.debug(f'Extracted coverage for {len(coverage_results)} files.')

    # Filter for low coverage
    low_coverage_files = [res for res in coverage_results if min_threshold <= res[1] < threshold]

    # Sort by coverage percentage (ascending)
    low_coverage_files.sort(key=lambda item: item[1])

    return low_coverage_files


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Analyze coverage files to find low line coverage.')
    parser.add_argument(
        '--fastcov-json',
        default='coverage.json',
        nargs='?',
        type=str,
        help='Path to the fastcov coverage.json file.',
    )
    parser.add_argument(
        '--threshold',
        type=float,
        default=80.0,
        help='Upper coverage threshold percentage (0-100). Files below this threshold will be reported. Default: 80.0',
    )
    parser.add_argument(
        '--min-threshold',
        type=float,
        default=0.0,
        help='Lower coverage threshold percentage (0-100). Files at or above this threshold will be considered. Default: 0.0',
    )

    args = parser.parse_args()

    if not 0.0 <= args.threshold <= 100.0:
        logger.error('Threshold must be between 0.0 and 100.0')
        exit(1)
    if not 0.0 <= args.min_threshold <= 100.0:
        logger.error('Min-threshold must be between 0.0 and 100.0')
        exit(1)
    if args.min_threshold >= args.threshold:
        logger.error('Min-threshold must be less than threshold.')
        exit(1)

    low_coverage = find_low_coverage_from_json(args.fastcov_json, args.threshold, args.min_threshold)

    if low_coverage:
        if args.min_threshold > 0.0:
            logger.info(
                f'\n--- Files with Line Coverage Between {args.min_threshold:.2f}% and {args.threshold:.2f}% (from {args.fastcov_json}) ---',
            )
        else:
            logger.info(
                f'\n--- Files with Line Coverage Below {args.threshold:.2f}% (from {args.fastcov_json}) ---',
            )
        for source_file, coverage in low_coverage:
            logger.info(f'{coverage:.2f}% : {source_file}')
        logger.info('--------------------------------------------------------------------')
    else:
        if args.min_threshold > 0.0:
            logger.info(
                f'\nNo files found with line coverage between {args.min_threshold:.2f}% and {args.threshold:.2f}% in {args.fastcov_json}.',
            )
        else:
            logger.info(f'\nNo files found with line coverage below {args.threshold:.2f}% in {args.fastcov_json}.')
