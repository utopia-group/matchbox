
from argparse import ArgumentParser


def make_ip_rule(i):
    assert isinstance(i, int)
    # Support up to 16,777,216 rules (256^3) using three bytes
    third_byte = i // 65536
    snd_byte = (i % 65536) // 256
    lo_byte = i % 256
    return "ADD,ipv4,10.{0}.{1}.{2}/32#32,{3}{3}#48;{3}#9,0".format(third_byte, snd_byte, lo_byte, i)

def make_ethernet_rule(i):
    assert isinstance(i, int)
    # Support large numbers by using the full MAC address space
    # MAC address is 48 bits, so we can support very large i values
    return "ADD,ethernet,{0}{0}#48,{0}#9,0".format(i)

def make_punt_rule():
    return "ADD,punt,0&0#16;1#1;0&0#4;0&0#32;0&0#32;0#8,,0"

def main ():
    parser = ArgumentParser(description="Generate n insertions into logical.p4")
    parser.add_argument('num_inserts', metavar="N", type=int,
                        help="The number of insertions to generate")

    args = parser.parse_args()
    max_inserts = int((args.num_inserts - 3) / 2)

    rules = [make_ip_rule(1),
             make_ethernet_rule(1),
             make_punt_rule()]
    rules.extend([ make_ethernet_rule(i + 2) for i in range(max_inserts)])
    rules.extend([ make_ip_rule(i + 2) for i in range(max_inserts)])

    for r in rules:
        print (r)


if __name__ == "__main__" : main()
