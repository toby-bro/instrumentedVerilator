import os
import re
from pathlib import Path

import matplotlib.pyplot as plt
import pandas as pd


def read_coverage_files(coverage_dir: str) -> pd.DataFrame:
    coverage_data = []
    coverage_path = Path(coverage_dir)

    # Get all .cov files
    cov_files = list(coverage_path.glob('**/*.covslang'))

    if not cov_files:
        raise ValueError(f'No .cov files found in {coverage_dir}')

    # Read each file and extract coverage data
    for file_path in cov_files:
        try:
            with open(file_path, 'r') as f:
                lines = f.read().strip().split('\n')

            if len(lines) != 3:
                print(f"Warning: {file_path.name} doesn't have exactly 3 lines, skipping...")
                continue

            # Parse coverage values (function, line, branch)
            function_coverage = float(lines[0])
            line_coverage = float(lines[1])
            branch_coverage = float(lines[2])

            # Get file modification time for ordering
            file_time = os.path.getmtime(file_path)

            # Extract file number for additional ordering info
            file_number = None
            match = re.search(r'(\d+)\.cov', file_path.name)
            if match:
                file_number = int(match.group(1))

            coverage_data.append(
                {
                    'filename': file_path.name,
                    'file_number': file_number,
                    'timestamp': file_time,
                    'function_coverage': function_coverage,
                    'line_coverage': line_coverage,
                    'branch_coverage': branch_coverage,
                },
            )

        except Exception as e:
            print(f'Error reading {file_path.name}: {e}')
            continue

    if not coverage_data:
        raise ValueError('No valid coverage data found')

    # Create DataFrame and sort by branch coverage values
    df = pd.DataFrame(coverage_data)
    df = df.sort_values('branch_coverage').reset_index(drop=True)

    # Add a sequence number for plotting
    df['sequence'] = range(len(df))

    return df


def plot_coverage_evolution(df: pd.DataFrame, output_file: str | None = None) -> None:
    """
    Plot the evolution of function, line, and branch coverage over time.
    """
    plt.figure(figsize=(12, 5))

    # Create the plot with different line styles for each coverage type
    plt.plot(
        df['sequence'],
        df['line_coverage'],
        linewidth=4,
        linestyle='-',  # solid line
        label='VF L',
        color='blue',
    )

    plt.plot(
        df['sequence'],
        df['function_coverage'],
        linewidth=4,
        linestyle='--',  # dashed line
        label='VF F',
        color='orange',
    )

    plt.plot(
        df['sequence'],
        df['branch_coverage'],
        linewidth=4,
        # marker='+',  # crosses
        markersize=4,
        linestyle='-.',  # solid line with crosses
        label='VF B',
        color='green',
    )

    # Add Verismith coverage reference lines
    plt.axhline(y=16.6, color='grey', linestyle='--', linewidth=2, label='VS F (16.6%)')
    plt.axhline(y=15.1, color='grey', linestyle='-', linewidth=2, label='VS L (15.1%)')
    plt.axhline(y=11.4, color='grey', linestyle='-.', linewidth=2, label='VS B (11.4%)')

    # Find intersection where branch coverage crosses Verismith baseline
    verismith_branch = 11.4

    # Find the crossing point where branch coverage exceeds Verismith baseline
    crossing_indices = df[df['branch_coverage'] >= verismith_branch].index
    if len(crossing_indices) > 0:
        crossing_index = crossing_indices[0]
        # Get the sequence number for the crossing point
        crossing_x = float(df.loc[crossing_index, 'sequence'])

        # If there's a previous point, interpolate for more precision
        if crossing_index > 0:
            prev_index = crossing_index - 1
            y1 = float(df.loc[prev_index, 'branch_coverage'])
            y2 = float(df.loc[crossing_index, 'branch_coverage'])
            x1 = float(df.loc[prev_index, 'sequence'])
            x2 = float(df.loc[crossing_index, 'sequence'])

            # Linear interpolation to find exact crossing point
            if y2 != y1:  # Avoid division by zero
                crossing_x = x1 + (verismith_branch - y1) * (x2 - x1) / (y2 - y1)

        # plt.axvline(
        #     x=crossing_x,
        #     color='red',
        #     linestyle='--',
        #     linewidth=2,
        #     label=f'Verismith Parity Point (#{int(crossing_x)})',
        # )

    # Find the maximal coverage point for each metric and print it
    max_function_coverage = df['function_coverage'].max()
    max_line_coverage = df['line_coverage'].max()
    max_branch_coverage = df['branch_coverage'].max()

    print(f'Maximal Function Coverage: {max_function_coverage:.1f}%')
    print(f'Maximal Line Coverage: {max_line_coverage:.1f}%')
    print(f'Maximal Branch Coverage: {max_branch_coverage:.1f}%')

    print(f'Function Coverage boost: {max_function_coverage/0.166:.1f}%')
    print(f'Line Coverage boost:     {max_line_coverage/0.151:.1f}%')
    print(f'Branch Coverage boost:   {max_branch_coverage/0.17:.1f}%')

    # Customize the plot
    plt.xlabel('Number of files', fontsize=24)
    plt.ylabel('Coverage Percentage (%)', fontsize=24)
    # plt.title('Coverage Evolution of Verilator', fontsize=28, fontweight='bold')
    plt.legend(fontsize=22, framealpha=1, ncol=3, loc='lower right')
    plt.grid(True, alpha=0.3)

    # Set tick label font sizes
    plt.xticks(fontsize=20)
    plt.yticks(fontsize=20)
    # Start Y at zero
    plt.ylim(0, 60)

    # Add some padding to x-axis
    plt.xlim(-0.5, len(df) - 0.5)

    # Improve layout
    plt.tight_layout()

    # Save or show the plot
    if output_file:
        plt.savefig(output_file, dpi=300, bbox_inches='tight')
        print(f'Plot saved to {output_file}')
    else:
        plt.show()


def main() -> int:
    """
    Main function to read coverage data and create the evolution plot.
    """
    coverage_dir = 'coverage_evolution_non_empty/slang/'
    output_file = 'coverage_evolution.pdf'

    try:
        # Read coverage data
        print(f'Reading coverage files from {coverage_dir}...')
        df = read_coverage_files(coverage_dir)

        print(f'Found {len(df)} valid coverage files')
        print('\nCoverage data summary:')
        print(df[['filename', 'function_coverage', 'line_coverage', 'branch_coverage']].to_string(index=False))

        # Create the plot
        print('\nCreating coverage evolution plot...')
        plot_coverage_evolution(df, output_file)

        # Display some statistics
        print('\nCoverage Statistics:')
        print(f"Function Coverage: {df['function_coverage'].min():.1f}% - {df['function_coverage'].max():.1f}%")
        print(f"Line Coverage: {df['line_coverage'].min():.1f}% - {df['line_coverage'].max():.1f}%")
        print(f"Branch Coverage: {df['branch_coverage'].min():.1f}% - {df['branch_coverage'].max():.1f}%")

    except Exception as e:
        print(f'Error: {e}')
        return 1

    return 0


if __name__ == '__main__':
    exit(main())
