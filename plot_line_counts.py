import logging
import os
import subprocess

import matplotlib.pyplot as plt


def plot_line_counts(output_image='line_counts.png'):
    """
    Plots the number of lines for each naive/*.sv file and indicates
    slang validity with color.
    """
    file_numbers = []
    line_counts = []
    colors = []

    for i in range(152):
        file_path = f'naive/{i}.sv'
        if os.path.exists(file_path):
            file_numbers.append(i)

            # Get line count
            try:
                wc_result = subprocess.run(['wc', '-l', file_path], capture_output=True, text=True, check=True)
                line_counts.append(int(wc_result.stdout.split()[0]))
            except (subprocess.CalledProcessError, IndexError, ValueError) as e:
                logging.error(f'Could not get line count for {file_path}: {e}')
                line_counts.append(0)

            # Check slang validity
            try:
                slang_result = subprocess.run(
                    ['slang', '--error-limit=0', file_path], capture_output=True, text=True, check=False
                )
                if slang_result.returncode == 0:
                    colors.append('g')  # Green for valid
                else:
                    colors.append('r')  # Red for invalid
            except FileNotFoundError:
                logging.error("slang command not found. Please ensure it's in your PATH.")
                colors.append('gray')  # Gray for unknown
            except Exception as e:
                logging.error(f'An error occurred while running slang on {file_path}: {e}')
                colors.append('gray')

    if not file_numbers:
        logging.info('No naive/*.sv files found to plot.')
        return

    plt.figure(figsize=(20, 6))
    plt.bar(file_numbers, line_counts, color=colors)
    plt.xlabel('File Number (naive/X.sv)')
    plt.ylabel('Number of Lines')
    plt.title('Number of Lines per File (Green=Valid, Red=Invalid)')
    plt.grid(axis='y', alpha=0.75)

    # Create a custom legend
    from matplotlib.patches import Patch

    legend_elements = [
        Patch(facecolor='g', edgecolor='g', label='Valid Slang'),
        Patch(facecolor='r', edgecolor='r', label='Invalid Slang'),
    ]
    plt.legend(handles=legend_elements)

    plt.savefig(output_image, dpi=300)
    logging.info(f'Plot saved to {output_image}')


if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO, format='%(levelname)s - %(message)s')
    plot_line_counts()
