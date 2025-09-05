from pathlib import Path

import json
import datetime

import tyro

from eval.experiments import experiments

def run(
    dir: Path,
    trials: int = 3,
):
    stats_dir = dir / Path('stats')
    if not stats_dir.exists():
        stats_dir.mkdir(parents=True)
    elif not stats_dir.is_dir():
        raise NotADirectoryError(f'{stats_dir} exists and is not a directory')

    exps = experiments(trials)

    max_time = 0
    to_run = []
    for exp in exps:
        for run in exp.to_run(stats_dir):
            to_run.append(run)
            max_time += (run.timeout if run.timeout else 0)

    delta = datetime.timedelta(seconds=max_time)

    n_to_run = len(to_run)
    for run in to_run:
        print(f'experiments to run: {n_to_run}, max time: {delta}')
        run.run(stats_dir)
        n_to_run -= 1
        delta -= datetime.timedelta(seconds=(run.timeout if run.timeout else 0))

def eval(
    dir: Path,
    trials: int = 3,
):
    stats_dir = dir / Path('stats')
    data_dir = dir / Path('data')
    data_dir.mkdir(parents=True, exist_ok=True)
    exps = experiments(trials)
    for exp in exps:
        exp.evaluate(stats_dir, data_dir)

if __name__ == '__main__':
    tyro.extras.subcommand_cli_from_dict(
        {
            "run": run,
            "eval": eval,
        }
    )