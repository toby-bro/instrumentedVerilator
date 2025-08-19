import numpy as np
import pandas as pd
from scipy import stats


def calculate_confidence_interval(file_path: str, confidence_level: float = 0.95) -> None:
    """
    Calculates a confidence interval for the mean of scores from a file.

    Args:
        file_path (str): The path to the file containing the scores.
        confidence_level (float): The desired confidence level for the interval.
    """
    try:
        # Read the scores into a pandas DataFrame
        scores = pd.read_csv(file_path, header=None, names=['score'])

        # Extract the scores as a numpy array
        data = scores['score'].values

        # Get the number of observations
        n = len(data)

        # Calculate the sample mean
        mean = np.mean(data)

        # Calculate the sample standard deviation
        std_dev = np.std(data, ddof=1)

        # Calculate the standard error of the mean (SEM)
        sem = stats.sem(data)

        # Calculate the confidence interval
        confidence_interval = stats.t.interval(confidence_level, n - 1, loc=mean, scale=sem)

        # Print the results
        print(f'Confidence Interval Calculation (Confidence Level: {confidence_level * 100}%)')
        print('-' * 50)
        print(f'Number of observations (n): {n}')
        print(f'Sample Mean: {mean:.4f}')
        print(f'Standard Deviation (Écart type): {std_dev:.4f}')
        print(f'Standard Error of the Mean (SEM): {sem:.4f}')
        print(f'Confidence Interval: ({confidence_interval[0]:.4f}, {confidence_interval[1]:.4f})')
        print('-' * 50)
        print(
            f'This means we are {confidence_level * 100}% confident that the true population mean of the scores lies between {confidence_interval[0]:.4f} and {confidence_interval[1]:.4f}.',
        )

    except FileNotFoundError:
        print(f"Error: The file '{file_path}' was not found.")
    except Exception as e:
        print(f'An error occurred: {e}')


if __name__ == '__main__':
    calculate_confidence_interval('score.sscrs')
