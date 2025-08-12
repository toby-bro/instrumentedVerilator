import logging
import re

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.ticker import PercentFormatter


def plot_attempts_histogram(log_file='attempts.log', output_image='attempts_histogram.png'):
    """
    Parses the log file to find the number of attempts for each successful generation,
    and plots a histogram of these attempt counts.

    Args:
        log_file (str): The path to the log file.
        output_image (str): The path to save the output histogram image.
    """
    attempt_counts = []
    last_attempt_num = 0

    try:
        with open(log_file, 'r') as f:
            for line in f:
                match = re.search(r'Attempt (\d+) of \d+', line)
                if match:
                    current_attempt_num = int(match.group(1))
                    if current_attempt_num == 1 and last_attempt_num > 0:
                        attempt_counts.append(last_attempt_num)
                    last_attempt_num = current_attempt_num

            # Add the last sequence of attempts
            if last_attempt_num > 0:
                attempt_counts.append(last_attempt_num)

    except FileNotFoundError:
        logging.error(f"Log file not found at '{log_file}'")
        return

    if not attempt_counts:
        logging.info('No attempt data found in the log file.')
        return

    # Plotting the histogram
    plt.figure(figsize=(10, 6))
    weights = np.ones_like(attempt_counts) / len(attempt_counts)
    plt.hist(attempt_counts, bins=range(1, max(attempt_counts) + 2), align='left', rwidth=0.8, weights=weights)
    plt.xlabel('Number of Attempts')
    plt.ylabel('Percentage of Files')
    plt.title('Histogram of Attempts to Generate a Correct File')
    plt.xticks(range(1, max(attempt_counts) + 1))
    plt.gca().yaxis.set_major_formatter(PercentFormatter(1))
    plt.grid(axis='y', alpha=0.75)

    # Save the plot
    plt.savefig(output_image)
    logging.info(f'Histogram saved to {output_image}')


if __name__ == '__main__':
    plot_attempts_histogram()
