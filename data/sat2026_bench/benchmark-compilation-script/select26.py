#!/usr/bin/env python3

import sys
from importlib.metadata import version, PackageNotFoundError
from packaging.version import Version

from gbd_core.api import GBD
import numpy as np
import polars as pl

REQUIREMENTS = {
    "gbd-tools": Version("5.0.1"),
    "polars": Version("1.36.1"),
}

def check_deps():
    for pkg, minimum_version in REQUIREMENTS.items():
        try:
            v = Version(version(pkg))
        except PackageNotFoundError:
            sys.exit(f"Missing dependency: {pkg}")

        if v < minimum_version:
            sys.exit(f"{pkg} version {v} does not satisfy >= {minimum_version}")


def main():
    check_deps()
    
    # Select benchmarks from new submissions:
    seeds = np.random.default_rng(seed=2026)
    newb = pl.DataFrame()
    
    b26 = GBD(["benchmarks2026.csv"])
    df = b26.query("participates=yes", resolve=["hash", "author", "family", "result"], collapse="min", group_by="isohash2")
    for a in df["author"].unique():
        fdf = df.filter(pl.col("author") == a)
        budget = 12
        sample = fdf.sample(n=min(budget, len(fdf)), seed=int(seeds.integers(0, 2**31)))
        newb = pl.concat([newb, sample])
        
    df = b26.query("participates=no", resolve=["hash", "author", "family", "result"], collapse="min", group_by="isohash2")
    for a in df["family"].unique():
        fdf = df.filter(pl.col("family") == a)
        budget = 16
        sample = fdf.sample(n=min(budget, len(fdf)), seed=int(seeds.integers(0, 2**31)))
        newb = pl.concat([newb, sample])
        
    print("Selected", len(newb), "benchmarks from new submissions")
    print(newb["result"].value_counts())
    
    # Hash over new benchmarks is seed for selection of old benchmarks
    new_seed = hash("|".join(newb["hash"].sort())) % (2**32)
    seeds = np.random.default_rng(seed=new_seed)
    
    # Calculate budget for old benchmarks:
    budget = 400 - len(newb)
    count_sat = len(newb.filter(pl.col("result") == "sat"))
    count_unsat = len(newb.filter(pl.col("result") == "unsat"))    
    budget_sat = (budget // 3) + (count_unsat - count_sat) // 2
    budget_unsat = (budget // 3) + (count_sat - count_unsat) // 2
    budget_unknown = budget - budget_sat - budget_unsat
    
    gbd = GBD(["meta.db"])
    allb = gbd.query("minisat1m != yes and family unlike %random% and huge=no", resolve=["hash", "track", "family", "author", "result"], collapse="min", group_by="isohash2")
    
    # Parse track information and extract year of first track in which the benchmark was used:
    allb = allb.with_columns(
        pl.when(pl.col("track").is_null() | (pl.col("track") == "")).then(pl.lit(0))  # null or empty track
            .when(pl.col("track").str.contains("submissions_") & ~pl.col("track").str.contains(",")).then(pl.lit(2025))  # newer unused submission
            .otherwise(pl.col("track").str.extract_all(r"(\d{4})").list.min().fill_null(0).cast(pl.Int32))
            .alias("firstuse")
    )
    
    # Calculate weights based on firstuse year
    def get_year_weight(firstuse):
        if 2017 <= firstuse <= 2025:  # linear increase from 2016 to 2025
            return 0.8 * (firstuse - 2016) / (2025 - 2016)
        else:  # before 2016 or notrack
            return 0.2  # 20% budget

    allb = allb.with_columns(
        pl.col("firstuse").map_elements(get_year_weight).alias("year_weight")
    )
    
    # Calculate author and family weights based on counts
    author_lookup = dict(allb.group_by("author").len().rows())
    family_lookup = dict(allb.group_by("family").len().rows())
    
    # Calculate author and family weights: smaller groups get higher weights (100/count)
    allb = allb.with_columns(
        pl.col("author").map_elements(lambda x: 100 / author_lookup.get(x, 1)).alias("author_weight"),
        pl.col("family").map_elements(lambda x: 100 / family_lookup.get(x, 1)).alias("family_weight")
    )

    # Normalize weights to sum to 100
    allb = allb.with_columns(
        (pl.col("year_weight") + pl.col("author_weight") + pl.col("family_weight")).alias("weight")
    )
    
    # Select benchmarks from old ones based on result and weights:
    def weighted_sample(df, n, weights_col, seed_val):
        if len(df) == 0:
            return df
        weights = df[weights_col].to_numpy()
        n = min(n, len(df))
        rng = np.random.default_rng(seed=seed_val)
        indices = rng.choice(len(df), size=n, p=weights/weights.sum(), replace=False)
        return df[indices]
    
    satsam = weighted_sample(allb.filter(pl.col("result") == "sat"), budget_sat, "weight", int(seeds.integers(0, 2**31)))
    unssam = weighted_sample(allb.filter(pl.col("result") == "unsat"), budget_unsat, "weight", int(seeds.integers(0, 2**31)))
    unksam = weighted_sample(allb.filter(pl.col("result") == "unknown"), budget_unknown, "weight", int(seeds.integers(0, 2**31)))
 
    satsam = satsam.select(["isohash2", "hash", "author", "family", "result"])
    unssam = unssam.select(["isohash2", "hash", "author", "family", "result"])
    unksam = unksam.select(["isohash2", "hash", "author", "family", "result"])
 
    oldb = pl.concat([satsam, unssam, unksam]).sort("isohash2")
    
    print("Selected", len(oldb), "benchmarks from old ones")
    print(oldb["result"].value_counts())
        
    benchmarks = pl.concat([newb, oldb])
    
    print("Selected", len(benchmarks), "benchmarks in total")
    print(benchmarks["result"].value_counts())
    print(benchmarks["family"].value_counts())
    print(benchmarks["author"].value_counts())
    
    benchmarks.write_csv("selected_benchmarks.csv")


if __name__ == "__main__":
    main()