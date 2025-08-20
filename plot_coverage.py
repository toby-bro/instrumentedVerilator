import matplotlib.pyplot as plt

# Coverage data
coverage_types = ['Function Coverage', 'Line Coverage', 'Branch Coverage']
percentages = [66.3, 61.3, 45.1]
covered = [4316, 27274, 18399]
total = [6514, 44522, 40840]

# Create figure and axis
fig, ax = plt.subplots(figsize=(10, 6))

# Define colors for each bar
colors = ['#2E8B57', '#4169E1', '#DC143C']  # Sea Green, Royal Blue, Crimson

# Create horizontal bar chart
bars = ax.barh(coverage_types, percentages, color=colors, alpha=0.8, edgecolor='black', linewidth=0.5)

# Customize the plot
ax.set_xlabel('Coverage Percentage (%)', fontsize=12, fontweight='bold')
# ax.set_title('Code Coverage Analysis', fontsize=16, fontweight='bold', pad=20)
ax.set_xlim(0, 100)

# Add percentage labels on the bars
for bar, percentage, cov, tot in zip(bars, percentages, covered, total, strict=True):
    width = bar.get_width()
    ax.text(
        width + 1,
        bar.get_y() + bar.get_height() / 2,
        f'{percentage}%\n({cov:,} of {tot:,})',
        ha='left',
        va='center',
        fontweight='bold',
        fontsize=10,
    )

# Add grid for better readability
ax.grid(axis='x', alpha=0.3, linestyle='--')
ax.set_axisbelow(True)

# Improve layout
plt.tight_layout()

# Add a subtle background color
ax.set_facecolor('#f8f9fa')

# Customize tick parameters
ax.tick_params(axis='both', which='major', labelsize=11)

# Save the plot
plt.savefig('coverage_histogram.png', dpi=300, bbox_inches='tight', facecolor='white')
plt.show()
