import matplotlib.pyplot as plt
import numpy as np
import pandas as pd


def plot_scores(file_path: str) -> None:
    """
    Reads scores from a file, divides by 10, and plots a histogram with:
    - 10 bins across [0,1]
    - y-axis as proportion (0..1)
    - x-axis 0..1
    """
    try:
        # Read the scores into a pandas DataFrame
        scores = pd.read_csv(file_path, header=None, names=['score'])
        # Convert to [0,1]
        scores['score'] = scores['score'] / 10.0

        # Plot histogram
        plt.figure(figsize=(10, 6))
        bins = [i / 10 for i in range(11)]  # 10 bins -> 11 edges from 0 to 1
        weights = np.ones(len(scores['score'])) * (1.0 / len(scores['score']))
        plt.hist(scores['score'], bins=bins, range=(0, 1), weights=weights, edgecolor='black', align='mid')

        # Axes setup
        plt.xlim(0, 1)
        plt.ylim(0, 1)
        plt.xticks(bins)
        plt.yticks(bins)
        plt.xlabel('Score')
        plt.ylabel('Proportion')
        plt.title('Distribution of Scores')
        plt.grid(axis='y', alpha=0.75)

        # Save
        plt.tight_layout()
        plt.savefig('scores_histogram.png')
        print('Histogram saved to scores_histogram.png')

    except FileNotFoundError:
        print(f"Error: The file '{file_path}' was not found.")
    except Exception as e:
        print(f'An error occurred: {e}')


if __name__ == '__main__':
    plot_scores('score.sscrs')
