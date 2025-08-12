import matplotlib.pyplot as plt
import pandas as pd

# File path for the data
file_path = '/home/jns/Documents/Berkeley/instrumentedVerilator/testFiles/naive.csv'

try:
    # Read the data using pandas. The separator is a space and there's no header.
    data = pd.read_csv(file_path, sep=' ', header=None)
    data.columns = ['line_coverage', 'function_coverage']

    # Filter out entries where line coverage is less than 10%
    data = data[data['line_coverage'] >= 15]
    data = data[data['function_coverage'] >= 10]

    # --- Statistical Calculations ---

    # Calculate statistics for line coverage
    line_stats = data['line_coverage'].describe()
    line_avg = data['line_coverage'].mean()
    line_median = data['line_coverage'].median()
    line_std = data['line_coverage'].std()

    # Calculate statistics for function coverage
    func_stats = data['function_coverage'].describe()
    func_avg = data['function_coverage'].mean()
    func_median = data['function_coverage'].median()
    func_std = data['function_coverage'].std()

    # --- Print Results ---

    print('--- Line Coverage Statistics ---')
    print(f'Average (Moyenne): {line_avg:.2f}')
    print(f'Median (Médiane): {line_median:.2f}')
    print(f'Standard Deviation (Écart-type): {line_std:.2f}')
    print('-' * 20)

    print('--- Function Coverage Statistics ---')
    print(f'Average (Moyenne): {func_avg:.2f}')
    print(f'Median (Médiane): {func_median:.2f}')
    print(f'Standard Deviation (Écart-type): {func_std:.2f}')
    print('-' * 20)

    # --- Box Plot Generation ---

    plt.figure(figsize=(10, 6))
    # The `whis` parameter can be used to set the whisker length.
    # For 95% confidence interval, we calculate the 2.5 and 97.5 percentiles.
    # whis=[2.5, 97.5] shows the range covering 95% of the data.
    data.boxplot(column=['line_coverage', 'function_coverage'], whis=[2.5, 97.5])

    plt.title('Box Plot of Line and Function Coverage (95% interval)')
    plt.ylabel('Coverage (%)')
    plt.grid(True, linestyle='--', alpha=0.6)

    # Save the plot to a file
    plot_filename = 'coverage_boxplot.png'
    plt.savefig(plot_filename)
    print(f'Plot saved as {plot_filename}')

    # Display the plot
    plt.show()


except FileNotFoundError:
    print(f'Error: The file was not found at {file_path}')
except Exception as e:
    print(f'An error occurred: {e}')
