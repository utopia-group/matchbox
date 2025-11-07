# eBPF Configuration Generators

This directory contains Python programs that generate configuration tables for various components in an eBPF-based network function chain.


## State Types

**Per-CPU State**
- Each CPU core maintains its own independent state
- Better performance due to reduced contention
    
**System-Wide State**
- Shared state across all CPU cores
- Ensures global consistency
- Includes CPU ID in matching criteria for load distribution

## Programs

### 1. Firewall (`firewall/fw.py`)

Generates firewall configuration tables for access control of the form `(IP, (port_low, port_high)) -> allow/deny`. Semantically, this rule implies that any flow from the given `IP` and port in the range `(port_low, port_high)` should be allowed (or denied).

#### Usage
```bash
python fw.py [options]
```

**Options:**
- `--state_type`: Choose between `per_cpu` or `system_wide` (default: `system_wide`)
- `--num_configs`: Number of configurations to generate (default: 100)
- `--rules_file`: File containing IP/port rules (format: `ip_mask,port` per line)
- `--output_file`: Output JSON file (default: `firewall_{state_type}.json`)

**Rule Format:**
- Classbench generated seed (see `rules/` for samples).

**Generated Configuration:**
Generates a list of firewall tables in JSON format, where each entry itself is a list of rules. Each rule contains:
- Table: `firewall`
- Matches on IP mask and port range (for system-wide states: also includes random CPU ID assignment)
- Action: `allow`


### 2. Rate Limiter (`ratelimit/ratelimit.py`)

Generates rate limiter configuration tables for controlling the rate of incoming requests, using rates of the form `() -> limit`.

#### Usage
```bash
python ratelimit.py [options]
```

**Options:**
- `--limit_type`: Choose between `per_cpu` or `system_wide` (default: `system_wide`)
- `--num_configs`: Number of configurations to generate (default: 100)
- `--output_file`: Output JSON file (default: `lb_{lb_type}.json`)

**Generated Configuration:**
Generates a list of rate limiting configurations in JSON format, where each entry itself is a list of rules. Each rule contains:
- Table: `rate_limit`
- Matches on empty criteria
- Action: `limit`
- Data: Includes either `per_cpu_limit` or `system_wide_limit` based on the selected state type. Also includes `num_cpus` for translation purposes.

### 3. Router (`router/route.py`)

Generates routing configuration tables for packet forwarding decisions of the form `IP, src_port -> destination_port`.

#### Usage
```bash
python route.py [options]
```

**Options:**
- `--state_type`: Choose between `per_cpu` or `system_wide` (default: `system_wide`)
- `--num_configs`: Number of configurations to generate (default: 100)
- `--rules_file`: File containing IP/port mappings
- `--output_file`: Output JSON file (default: `route_{state_type}.json`)

**Generated Configuration:**
Generates a list of port forwarding tables in JSON format, where each entry itself is a list of rules. Each rule contains:
- Table: `port_forward`
- Matches on IP mask and src port (and CPU ID for system-wide)
- Action: `forward`
- Includes destination port in action data
