"""This file has code used across several testbenches."""

from pathlib import Path

VERILATOR_FLAGS = [
    '--assert',
    '-Wall',
    '-Wno-DECLFILENAME',
    '--trace',
    '--trace-fst',
    '--trace-structs',
    # NB: --trace-max-array must be ≥ size of the memory (in 4B words) for memory to appear in the waveforms
    '--trace-max-array',str(2**18)
    ]

# directory where our simulator will compile our tests + code
SIM_BUILD_DIR = "sim_build"

# simulator to use
SIM = "verilator"

# temporary file used to hold assembler output
TEMP_MACHINE_CODE_FILE = ".tmp.riscv.o"

# offset to map from standard Linux/ELF addresses to what our processor's memory uses
BIN_2_MEMORY_ADDRESS_OFFSET = 0x80000000

# assembler program
ASSEMBLER = 'riscv64-unknown-elf-as'

# readelf program
READELF = 'riscv64-unknown-elf-readelf'

RISCV_TESTS_PATH = Path('../../riscv-tests/isa')
RISCV_BENCHMARKS_PATH = Path('../../riscv-tests/benchmarks')

POINTS_FILE = 'points.json'

def assertEquals(expected, actual, msg=''):
    """Wrapper around regular assert, with automatic formatting of values in hex"""
    if expected != actual:
        assert_msg = f'expected {int(expected):#X} but was {int(actual):#X}'
        if msg != '':
            assert_msg += f': {msg}'
            pass
        assert expected == actual, assert_msg
        pass
    pass

def aggregateTestResults(*results):
    """Aggregates total/failed counts from all arguments, where each argument is a call to cocotb.runner.get_results()"""
    total_tests = sum([r[0] for r in results])
    total_failed_tests = sum([r[1] for r in results])
    return { 
        'tests_total': total_tests,
        'tests_failed': total_failed_tests,
        'tests_passed': total_tests - total_failed_tests
        }
