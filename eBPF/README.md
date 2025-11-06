# eBPF Configuration Generators

This directory contains Python programs that generate configuration tables for various components in an eBPF-based network function chain.

## Programs

### 1. Firewall (`firewall/fw.py`)

Generates firewall configuration tables for access control of the form `(IP, port) -> allow/deny`.

#### State Types

**Per-CPU State**
- Each CPU core maintains its own independent state
- Better performance due to reduced contention
    
**System-Wide State**
- Shared state across all CPU cores
- Ensures global consistency
- Includes CPU ID in matching criteria for load distribution

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
- Input file should contain one rule per line: `IP_MASK,PORT`
- Example: `10.1.1.0/24,80`

**Generated Configuration:**
Generates a list of firewall tables in JSON format, where each entry itself is a list of rules. Each rule contains:
- Table: `firewall`
- Matches on IP mask and port (for system-wide states: also includes random CPU ID assignment)
- Action: `allow`


### 2. Load Balancer (`loadbalance/lb.py`)

Generates load balancer configuration tables for distributing traffic across multiple CPUs.

#### State Types

**Consistent Hashing**
- Uses bucket mapping for consistent hash distribution
- Includes system-wide rate limiting

**Plain Load Balancing**
- Simple round-robin or random distribution
- Per-CPU rate limiting

#### Usage
```bash
python lb.py [options]
```

**Options:**
- `--lb_type`: Choose between `consistent` or `plain` (default: `consistent`)
- `--num_configs`: Number of configurations to generate (default: 100)
- `--output_file`: Output JSON file (default: `lb_{lb_type}.json`)

**Generated Configuration:**
Generates a list of load balancing tables in JSON format, where each entry itself is a list of rules. Each rule contains:
- Table: `load_balance`
- Matches on IP mask
- Action: `load_balance`
- Includes CPU ID in action data for consistent hashing


### 3. Router (`router/route.py`)

Generates routing configuration tables for packet forwarding decisions of the form `IP -> destination_port`.

#### State Types

**Per-CPU State**
- Each CPU core maintains its own independent state
- Better performance due to reduced contention
    
**System-Wide State**
- Shared state across all CPU cores
- Ensures global consistency
- Includes CPU ID in matching criteria for load distribution

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
- Matches on IP mask (and CPU ID for system-wide)
- Action: `forward`
- Includes destination port in action data
