#!/usr/bin/env python3
"""Plot exact finite-chain results; these are not measured hardware seconds."""
import argparse
from fractions import Fraction
import json
import math
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


ROOT = Path(__file__).resolve().parents[1]


def rational(record):
    return Fraction(int(record['numerator_hex'], 16), int(record['denominator_hex'], 16))


def logarithm(value):
    return math.log10(value.numerator)-math.log10(value.denominator)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path, default=ROOT/'results/physical_sat.json')
    parser.add_argument('--out-dir', type=Path, default=ROOT/'results')
    args = parser.parse_args()
    report = json.loads(args.report.read_text())
    if not report['all_checks_passed']:
        raise ValueError('cannot plot an unsuccessful audit')
    args.out_dir.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({'font.size': 10, 'axes.spines.top': False, 'axes.spines.right': False,
                         'svg.hashsalt': 'physical-sat-audit-1'})
    fig, axes = plt.subplots(1, 3, figsize=(15, 4.7), layout='constrained')
    fig.suptitle('SAT as a spin system: equilibrium is not an arrival-time guarantee', fontsize=16, weight='bold')
    n = 16
    k = list(range(n+1))
    landscape = [n-j+2*j*(n-j) for j in k]
    ax = axes[0]
    ax.plot(k, landscape, color='#355c9a', marker='o', markersize=3)
    ax.scatter([0, n], [n, 0], c=['#b64c4c', '#158f7a'], s=55, zorder=3)
    ax.annotate('initial trap', (0, n), xytext=(2, 32), arrowprops={'arrowstyle': '->', 'color': '#b64c4c'})
    ax.annotate('solution', (n, 0), xytext=(10, 25), arrowprops={'arrowstyle': '->', 'color': '#158f7a'})
    ax.set(title='16 spins, constant pair couplings', xlabel='Number of one bits', ylabel='Unsatisfied clause positions')
    ax.set_xticks(range(0, n+1, 4))
    ax.grid(alpha=.18)

    cold = sorted((row for row in report['thermal_cases'] if rational(row['rho']) == Fraction(1, 2)
                   and row['variables'] <= 32), key=lambda row: row['variables'])
    hot = sorted((row for row in report['thermal_cases'] if rational(row['rho']) == 1
                  and row['variables'] <= 32), key=lambda row: row['variables'])
    restarts = [row for row in report['restart_controls'] if row['variables'] <= 32]
    ax = axes[1]
    ax.plot([r['variables'] for r in cold], [logarithm(rational(r['mean_ticks'])) for r in cold],
            'o-', color='#7850a0', label='Fixed cold: rho = 1/2')
    ax.plot([r['variables'] for r in hot], [logarithm(rational(r['mean_ticks'])) for r in hot],
            's-', color='#c27720', label='Fixed hot: rho = 1')
    ax.plot([r['variables'] for r in restarts],
            [logarithm(rational(r['mean_ticks_until_success_with_endpoint_restarts'])) for r in restarts],
            '^-', color='#158f7a', label='Uniform restarts, rho = 0')
    ax.set(title='Exact mean update counts', xlabel='Number of spins', ylabel='log10(expected ticks to solution)')
    ax.set_xticks([2, 8, 16, 24, 32])
    ax.legend(fontsize=8, loc='upper left')
    ax.grid(alpha=.18)

    ax = axes[2]
    equilibrium = [float(rational(r['stationary_ground_probability'])) for r in cold]
    hit_bounds = [float(min(Fraction(1), r['variables']**3/rational(r['first_exit_mean_ticks']))) for r in cold]
    ax.plot([r['variables'] for r in cold], equilibrium, 'o-', color='#355c9a', label='Solution probability at equilibrium')
    ax.plot([r['variables'] for r in cold], hit_bounds, 's--', color='#b64c4c', label='Hit by n^3 ticks: upper bound')
    ax.set(yscale='log', title='Cold chain from the initial trap', xlabel='Number of spins', ylabel='Probability (log scale)')
    ax.set_xticks([2, 8, 16, 24, 32])
    ax.legend(fontsize=8, loc='lower left')
    ax.grid(alpha=.18, which='both')
    fig.supxlabel('Easy, unit-forced CNFs. Classical local model; ticks are not hardware seconds. Restart preparation and detection cost extra polynomial work.', fontsize=9)
    fig.savefig(args.out_dir/'physical_sat.png', dpi=160, metadata={'Software': 'p-vs-np-lab'})
    fig.savefig(args.out_dir/'physical_sat.svg', metadata={'Date': None, 'Creator': 'p-vs-np-lab'})
    plt.close(fig)


if __name__ == '__main__':
    main()
