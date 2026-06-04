#!/usr/bin/env python3
"""
Reproduce all experiments from the MatchBox PLDI 2026 paper (Section 8).

Three case studies:
  1. Programmable Switch Evolution    (Section 8.1) — 30 translations, 10 config sizes up to ~10K rules
  2. Consistent Multi-Cloud Firewalls (Section 8.2) — 6 translations, 10 config sizes up to ~10K rules
  3. eBPF Architectural Changes       (Section 8.3) — 6 translations, 10 config sizes up to ~1.8K rules

Sampled configs go into gitignored subdirectories under programs/*/data/.
Experiment JSONs and results CSVs overwrite the tracked files so you can
`git diff` to verify correctness.

Usage:
  python experiments.py                  # full end-to-end reproduction
  python experiments.py --step run       # just run experiments (samples must exist)
  python experiments.py --step report    # just generate figures + print stats (results must exist)
  python experiments.py --case retarget  # only the switch evolution case study
  python experiments.py --case acl       # only the cloud firewall case study
  python experiments.py --case ebpf      # only the eBPF case study

Steps (executed in order):
  build     — compile OCaml binaries via dune
  generate  — create base JSON configs (skipped if they already exist)
  sample    — subsample base configs at 10 uniform sizes + generate experiment JSONs
  run       — run all experiments via `matchbox exp`
  report    — generate paper figures + print summary statistics (Tables 1-3)
"""

import argparse
import json
import random
import subprocess
import sys
import time
from collections import OrderedDict, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent

# ── Directories ──────────────────────────────────────────────────────────────
RETARGET_DIR  = ROOT / "programs" / "retargeting"
ACL_DIR       = ROOT / "programs" / "acl"
EBPF_DIR      = ROOT / "programs" / "ebpf"
EBPF_RULES    = EBPF_DIR / "classbench_rules.txt"

NUM_SAMPLES = 10  # 10 config sizes at uniform intervals


# ─────────────────────────────────────────────────────────────────────────────
# Helpers
# ─────────────────────────────────────────────────────────────────────────────

def sh(cmd, *, cwd=None):
    """Run a shell command, printing it first. Exit on failure."""
    print(f"  $ {cmd}")
    r = subprocess.run(cmd, shell=True, cwd=cwd or ROOT)
    if r.returncode != 0:
        sys.exit(r.returncode)


def sh_to_file(cmd, outpath, *, cwd=None):
    """Run a command, capturing stdout to a file."""
    print(f"  $ {cmd}  >  {Path(outpath).relative_to(ROOT)}")
    with open(outpath, "w") as f:
        r = subprocess.run(cmd, shell=True, cwd=cwd or ROOT,
                           stdout=f, stderr=subprocess.PIPE, text=True)
    if r.returncode != 0:
        print(r.stderr, file=sys.stderr)
        sys.exit(r.returncode)


def banner(msg):
    print(f"\n{'=' * 64}\n  {msg}\n{'=' * 64}")


def heading(msg):
    print(f"\n--- {msg} ---")


# ─────────────────────────────────────────────────────────────────────────────
# Sampling helpers
# ─────────────────────────────────────────────────────────────────────────────

def _is_wildcard(entry):
    """True if every match field is a catch-all (all-*, or 0…0/0)."""
    for v in entry.get("matches", {}).values():
        s = str(v)
        if all(c in "*/" for c in s):
            continue
        if "/" in s:
            parts = s.split("/")
            if len(parts) == 2 and parts[1] == "0" and all(c == "0" for c in parts[0]):
                continue
        return False
    return True


def _split_tables(data, table_names):
    """Split JSON entries by table name, separating catch-all rules."""
    tables = {t: [] for t in table_names}
    catchalls = {t: None for t in table_names}
    other = []
    for e in data:
        t = e.get("table", "")
        if t in tables:
            if _is_wildcard(e):
                catchalls[t] = e
            else:
                tables[t].append(e)
        else:
            other.append(e)
    return tables, catchalls, other


def _uniform_sizes(max_size, n):
    """Return n sizes uniformly spaced from 1 to max_size (inclusive)."""
    if n == 1:
        return [max_size]
    step = (max_size - 1) / (n - 1)
    sizes = [int(1 + i * step) for i in range(n)]
    sizes[-1] = max_size
    return sizes


def subsample_and_write(input_json, table_names, n, out_dir, base_name):
    """Subsample a JSON config at n uniform sizes. Returns list of (size, filepath)."""
    data = json.loads(Path(input_json).read_text())
    tables, catchalls, other = _split_tables(data, table_names)

    max_size = min(len(tables[t]) for t in table_names)
    sizes = _uniform_sizes(max_size, n)
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    results = []
    for size in sizes:
        sample = list(other)
        for t in table_names:
            sample.extend(tables[t][:size])
            if catchalls[t]:
                sample.append(catchalls[t])
        outpath = out_dir / f"{base_name}{size}.json"
        outpath.write_text(json.dumps(sample, indent=2))
        results.append((size, outpath))
        print(f"    {base_name}{size}.json  ({len(sample)} entries)")
    return results


def generate_experiment_json(template_json, sample_sizes, base_name, sample_dir, out_json):
    """Generate an experiment JSON by replicating a template for each sample size."""
    template = json.loads(Path(template_json).read_text())
    # Keep paths relative to repo root, matching the original format
    sample_dir_str = str(Path(sample_dir).relative_to(ROOT)).replace("\\", "/")
    experiments = []

    for size in sample_sizes:
        for exp in template:
            new = dict(exp)
            new["name"] = f"{exp['name']}_{size}"

            # Rewrite input path
            inp = exp["input"].split("/")[-1]
            if inp == f"{base_name}.json":
                new["input"] = f"{sample_dir_str}/{base_name}{size}.json"
            elif inp.startswith(f"{base_name}_"):
                suffix = inp[len(base_name):]
                new["input"] = f"{sample_dir_str}/{base_name}{size}{suffix}"
            else:
                new["input"] = f"{sample_dir_str}/{inp}"

            # Rewrite output path
            if exp.get("output"):
                out = exp["output"].split("/")[-1]
                if out.startswith(f"{base_name}_"):
                    suffix = out[len(base_name):]
                    new["output"] = f"{sample_dir_str}/{base_name}{size}{suffix}"
                elif f"_{base_name}.json" in out:
                    prefix = out[:-(len(base_name) + 5)]
                    new["output"] = f"{sample_dir_str}/{prefix}{base_name}{size}.json"
                else:
                    parts = out[:-5].split("_", 1)
                    if len(parts) == 2:
                        new["output"] = f"{sample_dir_str}/{parts[0]}{size}_{parts[1]}.json"
                    else:
                        new["output"] = f"{sample_dir_str}/{out}"

            experiments.append(new)

    Path(out_json).write_text(json.dumps(experiments, indent=4))
    print(f"    Wrote {Path(out_json).relative_to(ROOT)}  ({len(experiments)} experiments)")
    return experiments


# ─────────────────────────────────────────────────────────────────────────────
# Step 0: Build
# ─────────────────────────────────────────────────────────────────────────────

def do_build():
    banner("Step 0: Build")
    sh("dune build")


# ─────────────────────────────────────────────────────────────────────────────
# Step 1: Generate base configs (skipped if data already present)
# ─────────────────────────────────────────────────────────────────────────────

def _binstr(value, width):
    """Convert an integer to a zero-padded binary string of exactly *width* bits."""
    return format(value % (2 ** width), f"0{width}b")


def _generate_lo_json(num_rules, output_path):
    """Generate lo.json directly from synthetic IPv4/Ethernet/punt rules.

    Creates (num_rules - 3) / 2 entries each for ethernet and ipv4 tables,
    plus one punt entry and catch-all wildcard entries for each table.
    """
    max_inserts = (num_rules - 3) // 2
    indices = [1] + list(range(2, max_inserts + 2))

    ethernet = []
    for i in indices:
        match_val = int(f"{i}{i}")
        ethernet.append({
            "table": "ethernet",
            "matches": {"ethernet.dstAddr": _binstr(match_val, 48)},
            "action": ["fwd"],
            "data": {"port": _binstr(i, 9)},
            "priority": 100,
        })
    ethernet.append({
        "table": "ethernet", "matches": {"ethernet.dstAddr": "*" * 48},
        "action": ["fwd"], "data": {"port": "1" * 9}, "priority": 101,
    })

    ipv4 = []
    for i in indices:
        ip = (10 << 24) | ((i // 65536) << 16) | (((i % 65536) // 256) << 8) | (i % 256)
        match_val = int(f"{i}{i}")
        ipv4.append({
            "table": "ipv4",
            "matches": {"dstAddr": _binstr(ip, 32)},
            "action": ["fwd"],
            "data": OrderedDict([("ethernet.dstAddr", _binstr(match_val, 48)),
                                 ("port", _binstr(i, 9))]),
            "priority": 100,
        })
    ipv4.append({
        "table": "ipv4", "matches": {"dstAddr": "*" * 32},
        "action": ["fwd"], "data": {"ethernet.dstAddr": "1" * 48, "port": "1" * 9},
        "priority": 101,
    })

    punt = [
        {"table": "punt",
         "matches": OrderedDict([("dstAddr", "0" * 32), ("etherType", "0" * 16),
                                  ("isValid", "1"), ("srcAddr", "0" * 32),
                                  ("ttl", "0" * 8), ("version", "0" * 4)]),
         "action": ["drop"], "data": {}, "priority": 100},
        {"table": "punt",
         "matches": {"etherType": "*" * 16, "isValid": "*", "version": "*" * 4,
                     "srcAddr": "*" * 32, "dstAddr": "*" * 32, "ttl": "*" * 8},
         "action": ["nop"], "data": {}, "priority": 101},
    ]

    Path(output_path).write_text(json.dumps(ethernet + ipv4 + punt, indent=2))


def gen_retarget():
    heading("Retargeting: base logical config")
    lo_json = RETARGET_DIR / "data" / "lo.json"
    if lo_json.exists():
        print("    lo.json present — skipping.")
        return
    lo_json.parent.mkdir(parents=True, exist_ok=True)
    _generate_lo_json(5001, lo_json)
    n = len(json.loads(lo_json.read_text()))
    print(f"    Generated {lo_json.relative_to(ROOT)}  ({n} entries)")


def _parse_ip_cidr(ip_cidr):
    """'192.168.1.0/24' -> '11000000101010000000000100000000/24'."""
    if "/" not in ip_cidr:
        ip_cidr = f"{ip_cidr}/32"
    ip_part, prefix = ip_cidr.split("/")
    binary_ip = "".join(format(int(o), "08b") for o in ip_part.split("."))
    return f"{binary_ip}/{prefix}"


def _generate_acl_json(classbench_csv, output_path):
    """Convert ClassBench CSV to ACL JSON with acl + ipv4_state tables + catch-alls."""
    random.seed(42)
    all_rules = []
    with open(classbench_csv) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            fields = {}
            for part in line.split(","):
                if "=" in part:
                    k, v = part.split("=", 1)
                    fields[k.strip()] = v.strip()
            base = {
                "srcAddr":  _parse_ip_cidr(fields["nw_src"]) if "nw_src" in fields else "0" * 32 + "/0",
                "dstAddr":  _parse_ip_cidr(fields["nw_dst"]) if "nw_dst" in fields else "0" * 32 + "/0",
                "l4_sport": format(int(fields["tp_src"]), "016b") if "tp_src" in fields else "*" * 16,
                "l4_dport": format(int(fields["tp_dst"]), "016b") if "tp_dst" in fields else "*" * 16,
                "proto":    format(int(fields["nw_proto"]), "08b") if "nw_proto" in fields else "*" * 8,
            }
            is_in = str(random.randint(0, 1))
            all_rules.append({"table": "acl", "matches": dict(base, is_inbound=is_in),
                              "action": ["allow"], "data": {}, "priority": 100})
            all_rules.append({"table": "ipv4_state",
                              "matches": dict(base, is_inbound="1" if is_in == "0" else "0"),
                              "action": ["seen"], "data": {}, "priority": 100})

    # Replace last entry of each table with a catch-all (matching original acl.json)
    wc = {"srcAddr": "0" * 32 + "/0", "dstAddr": "0" * 32 + "/0",
          "l4_sport": "*" * 16, "l4_dport": "*" * 16, "proto": "*" * 8, "is_inbound": "*"}
    # Find and replace the last acl and last ipv4_state entries
    for i in range(len(all_rules) - 1, -1, -1):
        if all_rules[i]["table"] == "ipv4_state":
            all_rules[i] = {"table": "ipv4_state", "matches": dict(wc), "action": ["unseen"], "data": {}, "priority": 101}
            break
    for i in range(len(all_rules) - 1, -1, -1):
        if all_rules[i]["table"] == "acl":
            all_rules[i] = {"table": "acl", "matches": dict(wc), "action": ["deny"], "data": {}, "priority": 101}
            break

    Path(output_path).write_text(json.dumps(all_rules, indent=2))
    return len(all_rules)


def gen_acl():
    heading("ACL: base config from ClassBench")
    acl_json = ACL_DIR / "data" / "acl.json"
    if acl_json.exists():
        print("    acl.json present — skipping.")
        return
    classbench_csv = ACL_DIR / "classbench_acl_inserts_5000.csv"
    if not classbench_csv.exists():
        print(f"    ERROR: {classbench_csv.relative_to(ROOT)} not found")
        sys.exit(1)
    acl_json.parent.mkdir(parents=True, exist_ok=True)
    n = _generate_acl_json(classbench_csv, acl_json)
    print(f"    Generated {acl_json.relative_to(ROOT)}  ({n} entries)")


_EBPF_DEFS = {
    "firewall":  {"table": "acl",          "action": ["allow"],   "catchall": ["deny"]},
    "ratelimit": {"table": "rate_limit",   "action": ["limit"],   "catchall": ["nop"]},
    "router":    {"table": "port_forward", "action": ["forward"], "catchall": ["nop"]},
}
_NUM_CPUS = 32


def _parse_ebpf_rules(rules_file, program_type):
    """Parse ClassBench rules into [(binary_ip, (port1_bin, port2_bin)), ...]."""
    rule_list = {}
    with open(rules_file) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            parts = line.split("\t")
            ip = parts[0][1:].strip()
            if program_type == "router":
                s = parts[2].split(":")
                d = parts[3].split(":")
                p1 = random.randint(int(s[0].strip()), int(s[1].strip()))
                p2 = random.randint(int(d[0].strip()), int(d[1].strip()))
            else:
                pr = parts[2].split(":")
                p1, p2 = int(pr[0].strip()), int(pr[1].strip())
            rule_list[ip] = (p1, p2)
    return [(_parse_ip_cidr(ip), (format(p1, "016b"), format(p2, "016b")))
            for ip, (p1, p2) in rule_list.items()]


def _ebpf_rule_data(program_type, ports):
    if program_type == "ratelimit":
        return {"limit": format(random.randint(50, 200), "08b")}
    if program_type == "router":
        return {"src_port": ports[0], "dst_port": ports[1]}
    return {}


def _generate_ebpf_json(rules_file, state_type, program_type, output_path):
    """Generate one eBPF table config JSON (per_cpu or system_wide)."""
    defs = _EBPF_DEFS[program_type]
    tbl = defs["table"]
    if program_type == "ratelimit":
        random.seed(42)

    if rules_file and Path(rules_file).exists():
        rules = _parse_ebpf_rules(rules_file, program_type)
    else:
        defaults = {"10.10.1.1/32": (1000, 1000), "10.1.1.1/24": (5000, 5000)}
        rules = [(_parse_ip_cidr(ip), (format(p1, "016b"), format(p2, "016b")))
                 for ip, (p1, p2) in defaults.items()]

    config = []
    wc_ip = "0" * 32 + "/0"
    if state_type == "per_cpu":
        for cpu in range(_NUM_CPUS):
            for ip_mask, ports in rules:
                config.append({"table": f"{tbl}{cpu}", "matches": {"ip_mask": ip_mask},
                               "action": list(defs["action"]),
                               "data": _ebpf_rule_data(program_type, ports), "priority": 100})
            config.append({"table": f"{tbl}{cpu}", "matches": {"ip_mask": wc_ip},
                           "action": list(defs["catchall"]), "data": {}, "priority": 101})
    else:
        for cpu in range(_NUM_CPUS):
            for ip_mask, ports in rules:
                config.append({"table": tbl,
                               "matches": {"ip_mask": ip_mask, "cpu_id": format(cpu, "05b")},
                               "action": list(defs["action"]),
                               "data": _ebpf_rule_data(program_type, ports), "priority": 100})
        config.append({"table": tbl, "matches": {"ip_mask": wc_ip, "cpu_id": "*" * 5},
                       "action": list(defs["catchall"]), "data": {}, "priority": 101})

    Path(output_path).parent.mkdir(parents=True, exist_ok=True)
    Path(output_path).write_text(json.dumps(config, indent=2))
    return len(config)


def gen_ebpf():
    heading("eBPF: configs (firewall, rate limiter, router)")
    data_dir = EBPF_DIR / "data"
    expected = ["fwcpu.json", "fwsys.json", "limitcpu.json",
                "limitsys.json", "routecpu.json", "routesys.json"]
    missing = [f for f in expected if not (data_dir / f).exists()]
    if not missing:
        print("    All present — skipping.")
        return
    data_dir.mkdir(parents=True, exist_ok=True)
    for prog, cpu_out, sys_out in [
        ("firewall",  "fwcpu.json",    "fwsys.json"),
        ("ratelimit", "limitcpu.json", "limitsys.json"),
        ("router",    "routecpu.json", "routesys.json"),
    ]:
        for state, out in [("per_cpu", cpu_out), ("system_wide", sys_out)]:
            n = _generate_ebpf_json(str(EBPF_RULES), state, prog, data_dir / out)
            print(f"    {out}  ({n} entries)")


def do_generate(cases):
    banner("Step 1: Generate base configs")
    if "retarget" in cases:
        gen_retarget()
    if "acl" in cases:
        gen_acl()
    if "ebpf" in cases:
        gen_ebpf()


# ─────────────────────────────────────────────────────────────────────────────
# Step 2: Subsample + generate experiment JSONs
# ─────────────────────────────────────────────────────────────────────────────

def sample_retarget():
    heading("Retargeting: subsampling lo.json at 10 sizes")
    sample_dir = RETARGET_DIR / "data" / f"experiments{NUM_SAMPLES}_5K"
    samples = subsample_and_write(
        RETARGET_DIR / "data" / "lo.json", ["ethernet", "ipv4"],
        NUM_SAMPLES, sample_dir, "lo",
    )
    generate_experiment_json(
        RETARGET_DIR / "experiments.json",
        [s for s, _ in samples], "lo", sample_dir,
        RETARGET_DIR / f"experiments{NUM_SAMPLES}.json",
    )


def sample_acl():
    heading("ACL: subsampling acl.json at 10 sizes")
    sample_dir = ACL_DIR / "data" / f"experiments{NUM_SAMPLES}"
    samples = subsample_and_write(
        ACL_DIR / "data" / "acl.json", ["acl", "ipv4_state"],
        NUM_SAMPLES, sample_dir, "acl",
    )
    generate_experiment_json(
        ACL_DIR / "experiments.json",
        [s for s, _ in samples], "acl", sample_dir,
        ACL_DIR / f"experiments{NUM_SAMPLES}.json",
    )


def sample_ebpf():
    heading("eBPF: subsampling configs at 10 sizes")
    data_dir = EBPF_DIR / "data"
    sample_dir = data_dir / f"experiments{NUM_SAMPLES}"
    sample_dir.mkdir(parents=True, exist_ok=True)

    ebpf_configs = [
        ("fwcpu.json", "per_cpu"),    ("fwsys.json", "system_wide"),
        ("limitcpu.json", "per_cpu"), ("limitsys.json", "system_wide"),
        ("routecpu.json", "per_cpu"), ("routesys.json", "system_wide"),
    ]

    all_sizes = {}
    for filename, mode in ebpf_configs:
        base = filename[:-5]
        data = json.loads((data_dir / filename).read_text())

        if mode == "per_cpu":
            by_table = defaultdict(list)
            catchalls = {}
            for e in data:
                t = e["table"]
                (catchalls.__setitem__(t, e) if _is_wildcard(e)
                 else by_table[t].append(e))
            max_n = min(len(v) for v in by_table.values()) if by_table else 0
            sizes = _uniform_sizes(max_n, NUM_SAMPLES)
            for size in sizes:
                sample = []
                for t in sorted(by_table):
                    sample.extend(by_table[t][:size])
                    if t in catchalls:
                        sample.append(catchalls[t])
                (sample_dir / f"{base}{size}.json").write_text(json.dumps(sample, indent=2))
            print(f"    {base}: {len(sizes)} samples, {max_n} max rules/table")
        else:
            # System-wide: group by cpu_id (including the "*****" catch-all group).
            # The original sampling includes a wildcard entry per cpu_id group.
            # For wildcard detection, skip the cpu_id field (a per-cpu catch-all
            # has a specific cpu_id but wildcard ip_mask).
            def _is_ebpf_wildcard(e):
                for k, v in e.get("matches", {}).items():
                    if k == "cpu_id":
                        continue
                    s = str(v)
                    if all(c in "*/" for c in s):
                        continue
                    if "/" in s:
                        parts = s.split("/")
                        if len(parts) == 2 and parts[1] == "0" and all(c == "0" for c in parts[0]):
                            continue
                    return False
                return True

            cpu_groups = defaultdict(lambda: ([], None))
            for e in data:
                cpu_id = e.get("matches", {}).get("cpu_id", "")
                regular, wildcard = cpu_groups[cpu_id]
                if _is_ebpf_wildcard(e):
                    cpu_groups[cpu_id] = (regular, e)
                else:
                    regular.append(e)
                    cpu_groups[cpu_id] = (regular, wildcard)
            max_n = min(len(r) for r, _ in cpu_groups.values() if r) if cpu_groups else 0
            sizes = _uniform_sizes(max_n, NUM_SAMPLES)
            for size in sizes:
                sample = []
                for cpu_id in sorted(cpu_groups):
                    regular, wildcard = cpu_groups[cpu_id]
                    sample.extend(regular[:size])
                    if wildcard:
                        sample.append(wildcard)
                (sample_dir / f"{base}{size}.json").write_text(json.dumps(sample, indent=2))
            print(f"    {base}: {len(sizes)} samples, {max_n} max rules/cpu")
        all_sizes[base] = sizes

    # Generate experiment JSON (interleaved: all experiments per size, then next size)
    template = json.loads((EBPF_DIR / "experiments.json").read_text())
    # Iterate over sample indices (0..NUM_SAMPLES-1); each config may have a
    # slightly different max size, so look up the actual size per config.
    experiments = []
    for idx in range(NUM_SAMPLES):
        for exp in template:
            base = Path(exp["input"]).stem
            if base not in all_sizes:
                continue
            size = all_sizes[base][idx]
            new = dict(exp)
            new["name"] = f"{exp['name']}_{size}"
            new["input"] = f"{str(sample_dir.relative_to(ROOT))}/{base}{size}.json"
            experiments.append(new)
    exp_json = EBPF_DIR / f"experiments{NUM_SAMPLES}.json"
    exp_json.write_text(json.dumps(experiments, indent=4))
    print(f"    Wrote {exp_json.relative_to(ROOT)}  ({len(experiments)} experiments)")


def do_sample(cases):
    banner("Step 2: Subsample at 10 uniform sizes")
    if "retarget" in cases:
        sample_retarget()
    if "acl" in cases:
        sample_acl()
    if "ebpf" in cases:
        sample_ebpf()


# ─────────────────────────────────────────────────────────────────────────────
# Step 3: Run experiments
# ─────────────────────────────────────────────────────────────────────────────

def run_exp(exp_json, results_csv, label, batch_size=0):
    """Run experiments and write results CSV.

    If batch_size > 0, split experiments into batches of that size and run
    each in a separate matchbox process.  This bounds peak memory usage for
    expensive translation chains (e.g., retargeting la_db at large sizes).
    """
    if not Path(exp_json).exists():
        print(f"  SKIP {label}: {exp_json} not found")
        return
    heading(label)
    experiments = json.loads(Path(exp_json).read_text())
    expected = len(experiments)
    t0 = time.time()

    if batch_size <= 0 or expected <= batch_size:
        sh_to_file(f"dune exec -- matchbox exp {exp_json}", results_csv)
    else:
        # Run in batches, each in its own process to limit memory
        tmp_json = Path(exp_json).with_suffix(".batch.json")
        try:
            first = True
            for i in range(0, expected, batch_size):
                batch = experiments[i:i + batch_size]
                tmp_json.write_text(json.dumps(batch))
                tmp_csv = Path(results_csv).with_suffix(f".batch{i}.csv")
                sh_to_file(f"dune exec -- matchbox exp {tmp_json}", tmp_csv)
                with open(results_csv, "a" if not first else "w") as out:
                    for j, line in enumerate(open(tmp_csv)):
                        if j == 0 and not first:
                            continue
                        out.write(line)
                tmp_csv.unlink()
                first = False
        finally:
            tmp_json.unlink(missing_ok=True)

    elapsed = time.time() - t0
    actual = sum(1 for _ in open(results_csv)) - 1
    print(f"  {elapsed:.1f}s  ->  {Path(results_csv).relative_to(ROOT)}  ({actual}/{expected} experiments)")
    if actual < expected:
        print(f"  WARNING: only {actual} of {expected} experiments completed!")
        print("  The matchbox process may have been killed (OOM). Try closing other")
        print("  applications or running individual case studies with --case.")


def do_run(cases):
    banner("Step 3: Run experiments")

    if "retarget" in cases:
        # Run in batches of 30 (one per sample size) to bound memory usage.
        # The la_db/la_ev translations at large sizes produce 50K+ entry
        # intermediate configs and can OOM if all 300 run in one process.
        run_exp(RETARGET_DIR / f"experiments{NUM_SAMPLES}.json",
                RETARGET_DIR / "results.csv",
                f"Retargeting ({NUM_SAMPLES} sizes x 30 translations)",
                batch_size=30)
    if "acl" in cases:
        run_exp(ACL_DIR / f"experiments{NUM_SAMPLES}.json",
                ACL_DIR / "results.csv",
                f"ACL ({NUM_SAMPLES} sizes x 6 translations)")
    if "ebpf" in cases:
        run_exp(EBPF_DIR / f"experiments{NUM_SAMPLES}.json",
                EBPF_DIR / "results.csv",
                f"eBPF ({NUM_SAMPLES} sizes x 6 translations)")


# ─────────────────────────────────────────────────────────────────────────────
# Step 4: Generate paper figures (Figures 15-18)
# ─────────────────────────────────────────────────────────────────────────────

def _load_results():
    """Load the three results CSVs as pandas DataFrames."""
    import pandas as pd
    return (
        pd.read_csv(RETARGET_DIR / "results.csv"),
        pd.read_csv(ACL_DIR / "results.csv"),
        pd.read_csv(EBPF_DIR / "results.csv"),
    )


def _setup_plot_style():
    import matplotlib
    matplotlib.use("Agg")  # non-interactive backend (no display needed)
    import matplotlib.pyplot as plt
    plt.style.use("seaborn-v0_8-whitegrid")
    plt.rcParams["font.family"] = "serif"
    plt.rcParams["font.serif"] = ["Linux Libertine O", "Linux Libertine", "Libertine", "Times New Roman", "Times"]
    plt.rcParams["mathtext.fontset"] = "stix"
    plt.rcParams["font.size"] = 12
    plt.rcParams["axes.labelsize"] = 14
    plt.rcParams["axes.titlesize"] = 16
    plt.rcParams["xtick.labelsize"] = 12
    plt.rcParams["ytick.labelsize"] = 12
    # Use LaTeX rendering if available (produces paper-quality fonts).
    # Falls back gracefully in Docker or minimal environments.
    # Use LaTeX rendering if available (paper-quality libertine fonts).
    import shutil
    if shutil.which("latex") and shutil.which("kpsewhich"):
        try:
            r = subprocess.run(["kpsewhich", "binhex.tex"],
                               capture_output=True, timeout=5)
            if r.returncode == 0:
                plt.rcParams["text.usetex"] = True
                plt.rcParams["text.latex.preamble"] = (
                    r"\usepackage{libertine}\usepackage[libertine]{newtxmath}")
        except Exception:
            pass


_NAME_MAP = {
    "ad": "action_decompose", "ch": "choice", "db": "double",
    "ev": "early_validate", "la": "link_aggregation", "lo": "logical",
    "fwcpu": "firewall (per-cpu)", "fwsys": "firewall (system-wide)",
    "limitcpu": "rate_limiter (per-cpu)", "limitsys": "rate_limiter (system-wide)",
    "routecpu": "router (per-cpu)", "routesys": "router (system-wide)",
}


def _scatter_evaltime_by_source(df, output_path):
    """Figure 15 / 17 / 18: compilation time vs input size, colored by source pipeline."""
    import matplotlib.pyplot as plt

    df = df.copy()
    df["source"] = df["name"].str.split("_").str[0]
    sources = sorted(df["source"].unique())
    colors = plt.cm.Set2(range(len(sources)))
    cmap = dict(zip(sources, colors))
    if "ev" in cmap and "lo" in cmap:
        cmap["ev"], cmap["lo"] = cmap["lo"], cmap["ev"]
    if "limitsys" in cmap and "routesys" in cmap:
        cmap["limitsys"], cmap["routesys"] = cmap["routesys"], cmap["limitsys"]
    markers = ["o", "s", "^", "D", "v", "p", "*", "h"]
    mmap = dict(zip(sources, markers))

    fig, ax = plt.subplots(figsize=(3.5, 3.5))
    use_seconds = df["eval_time"].max() >= 10000
    for src in sources:
        sd = df[df["source"] == src]
        x = sd["eval_in_size"]
        y = sd["eval_time"] / 1000 if use_seconds else sd["eval_time"]
        ax.scatter(x, y, label=_NAME_MAP.get(src, src), marker=mmap[src], s=25,
                   facecolors="none", edgecolors=cmap[src], linewidth=0.8, alpha=1)

    ax.set_xlabel("Input Configuration Size")
    ax.set_ylabel("Compilation Time (s)" if use_seconds else "Compilation Time (ms)")
    ax.legend(frameon=False, fontsize=9, handletextpad=0.3, borderpad=0.5,
              labelspacing=0.4, columnspacing=1.0, handlelength=1.5, loc="best")
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.grid(False)
    plt.tight_layout()
    plt.savefig(output_path, dpi=2400, bbox_inches="tight", format="pdf")
    plt.close(fig)


def _scatter_outsize(df, output_path):
    """Figure 16: output config size vs input size, colored by target pipeline."""
    import matplotlib.pyplot as plt
    from matplotlib.ticker import FuncFormatter

    df = df.copy()
    df["target"] = df["name"].str.split("_").str[1]
    targets = sorted(df["target"].unique())
    colors = plt.cm.Set2(range(len(targets)))
    cmap = dict(zip(targets, colors))
    if "ev" in cmap and "lo" in cmap:
        cmap["ev"], cmap["lo"] = cmap["lo"], cmap["ev"]
    markers = ["o", "s", "^", "D", "v", "p", "*", "h"]
    mmap = dict(zip(targets, markers))

    fig, ax = plt.subplots(figsize=(3.5, 3.5))
    for tgt in targets:
        td = df[df["target"] == tgt]
        ax.scatter(td["eval_in_size"], td["eval_out_size"],
                   label=_NAME_MAP.get(tgt, tgt), marker=mmap[tgt], s=25,
                   facecolors="none", edgecolors=cmap[tgt], linewidth=0.8, alpha=1)

    ax.set_xlabel("Input Configuration Size")
    ax.set_ylabel("Output Configuration Size")
    ax.yaxis.set_major_formatter(FuncFormatter(
        lambda v, _: f"{int(v / 1000)}K" if v >= 10000 else f"{int(v)}"))
    ax.legend(frameon=False, fontsize=9, handletextpad=0.3, borderpad=0.5,
              labelspacing=0.4, columnspacing=1.0, handlelength=1.5, loc="best")
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.grid(False)
    plt.tight_layout()
    plt.savefig(output_path, dpi=2400, bbox_inches="tight", format="pdf")
    plt.close(fig)


def _print_table(df):
    """Print Table 1/2/3: per-program statistics (deterministic columns)."""
    n_programs = df["name"].str.rsplit("_", n=1).str[0].nunique()
    n_with_fds = (df.groupby(df["name"].str.rsplit("_", n=1).str[0])["num_fds"]
                  .first() > 0).sum()
    tt = df["typetime"] * 1000  # ms -> us
    print(f"  Programs:          {n_programs}")
    print(f"  AST Size:          min={df['size'].min()}, median={df['size'].median()}, max={df['size'].max()}")
    print(f"  Annotation Count:  min={df['num_fds'].min()}, median={df['num_fds'].median():.0f}, max={df['num_fds'].max()}"
          f"  ({n_with_fds} of {n_programs} programs require annotations)")
    print(f"  Typecheck (us):    min={tt.min():.0f}, median={tt.median():.0f}, max={tt.max():.0f}")


def _print_compilation(df):
    """Print compilation statistics referenced in the paper text."""
    dc = df.copy()
    dc["time_per_rule"] = dc["eval_time"] / dc["eval_in_size"]
    in_min, in_max = dc["eval_in_size"].min(), dc["eval_in_size"].max()
    avg_tpr = dc["time_per_rule"].mean() * 1000  # ms -> us
    print(f"  Input config sizes: {in_min} to {in_max}")
    print(f"  Avg time per rule:  {avg_tpr:.1f} us/rule")


def do_report():
    banner("Step 4: Figures and statistics")
    df_ret, df_acl, df_ebpf = _load_results()

    # Figures 15-18
    _setup_plot_style()
    out = ROOT / "_output"
    out.mkdir(parents=True, exist_ok=True)
    for fn, filename, desc in [
        (lambda p: _scatter_evaltime_by_source(df_ret, p),  "figure-15.pdf",
         "Figure 15: Evolution Runtimes"),
        (lambda p: _scatter_outsize(df_ret, p),              "figure-16.pdf",
         "Figure 16: Evolution Config Size"),
        (lambda p: _scatter_evaltime_by_source(df_acl, p),  "figure-17.pdf",
         "Figure 17: Cloud Runtimes"),
        (lambda p: _scatter_evaltime_by_source(df_ebpf, p), "figure-18.pdf",
         "Figure 18: eBPF Runtimes"),
    ]:
        heading(desc)
        fn(out / filename)
        print(f"    -> _output/{filename}")

    # Tables 1-3
    heading("Table 1 - Retargeting (Section 8.1)")
    _print_table(df_ret)
    _print_compilation(df_ret)

    heading("Table 2 - Cloud Firewalls (Section 8.2)")
    _print_table(df_acl)
    _print_compilation(df_acl)

    heading("Table 3 - eBPF (Section 8.3)")
    _print_table(df_ebpf)
    _print_compilation(df_ebpf)


# ─────────────────────────────────────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────────────────────────────────────

ALL_STEPS = ["build", "generate", "sample", "run", "report"]
ALL_CASES = ["retarget", "acl", "ebpf"]


def main():
    p = argparse.ArgumentParser(
        description="Reproduce MatchBox PLDI 2026 experiments",
        formatter_class=argparse.RawDescriptionHelpFormatter, epilog=__doc__,
    )
    p.add_argument("--step", choices=ALL_STEPS, action="append", default=None,
                   help="Run only these steps (repeatable; default: all)")
    p.add_argument("--case", choices=ALL_CASES, action="append", default=None,
                   help="Run only these case studies (repeatable; default: all)")
    args = p.parse_args()

    cases = args.case or ALL_CASES
    steps = args.step or ALL_STEPS

    banner("MatchBox Experiment Reproduction")
    print(f"  Cases : {', '.join(cases)}")
    print(f"  Steps : {', '.join(steps)}")
    t0 = time.time()

    if "build" in steps:
        do_build()
    if "generate" in steps:
        do_generate(cases)
    if "sample" in steps:
        do_sample(cases)
    if "run" in steps:
        do_run(cases)
    if "report" in steps:
        do_report()

    # Print a summary of generated outputs
    outputs = []
    if "run" in steps:
        for case, d in [("retarget", RETARGET_DIR), ("acl", ACL_DIR), ("ebpf", EBPF_DIR)]:
            if case in cases:
                outputs.append(str((d / "results.csv").relative_to(ROOT)))
    if "report" in steps:
        for i in range(15, 19):
            outputs.append(f"_output/figure-{i}.pdf")
    if outputs:
        banner("Generated outputs")
        for o in outputs:
            print(f"  {o}")

    banner(f"Done  ({time.time() - t0:.1f}s)")


if __name__ == "__main__":
    main()
