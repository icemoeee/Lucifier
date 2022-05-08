import tokenize
import zlib, base64
from tokenize import NUMBER, NAME, NEWLINE
import re
import math
import sys
import pickle
import json
import traceback
import signal
import time
import logging
import six
from collections import namedtuple
from utils import *
from constant import *
from vargenerator import *
from ethereum_data import *
from basicblock import BasicBlock
from analysis import *
from test_evm.global_test_params import (TIME_OUT, UNKNOWN_INSTRUCTION,
                                         EXCEPTION, PICKLE_PATH)
from vulnerability import Reentrancy, AssertionFailure
import global_params
from pysmt.typing import BVType
from pysmt.shortcuts import *
from pysmt.environment import get_env
get_env().enable_infix_notation = True

log = logging.getLogger(__name__)

UNSIGNED_BOUND_NUMBER = 2**256 - 1
# CONSTANT_ONES_159 = BitVecVal((1 << 160) - 1, 256)
CONSTANT_ONES_159 = BV(CONSTANT_ONE_160, 256)  # 是160个1

Assertion = namedtuple('Assertion', ['pc', 'model'])
Underflow = namedtuple('Underflow', ['pc', 'model'])
Overflow = namedtuple('Overflow', ['pc', 'model'])
class Global_Flags:
    call_flag = CONSTANT_UNLOCK
    sstore_flag = CONSTANT_UNLOCK
    path_index = 0
    call_target = 0

class Parameter:
    def __init__(self, **kwargs):
        attr_defaults = {
            "stack": [],
            "calls": [],
            "memory": [],
            "visited": [],
            "current_flow": [],
            "in_call_flow": [],
            "out_call_flow": [],
            "been_call": CONSTANT_UNLOCK,
            "reentry_key_pcs": [],
            "mem": {},
            "analysis": {},
            "sha3_list": {},
            "global_state": {},
            "path_conditions_and_vars": {},
            "new_path_conditions_and_vars": {},
            "current_function": []
        }
        for (attr, default) in six.iteritems(attr_defaults):
            setattr(self, attr, kwargs.get(attr, default))

    def copy(self):
        _kwargs = custom_deepcopy(self.__dict__)
        return Parameter(**_kwargs)

def initGlobalVars():
    global g_src_map
    global solver
    # Z3 solver

    # '''PARALLEL'''
    # if global_params.PARALLEL:
    #     t2 = Then('simplify', 'solve-eqs', 'smt')
    #     _t = Then('tseitin-cnf-core', 'split-clause')
    #     t1 = ParThen(_t, t2)
    #     solver = OrElse(t1, t2).solver()
    # else:
    #     solver = Solver()

    solver = Solver(name="yices", logic="QF_BV", incremental=True)
    # solver.set("timeout", global_params.TIMEOUT)

    global MSIZE
    MSIZE = False

    global revertible_overflow_pcs
    revertible_overflow_pcs = set()

    global g_disasm_file
    with open(g_disasm_file, 'r') as f:
        disasm = f.read()
    if 'MSIZE' in disasm:
        MSIZE = True

    global g_timeout
    g_timeout = False

    global visited_pcs
    visited_pcs = set()

    global results
    # if g_src_map:  # not bytecode
    global start_block_to_func_sig
    start_block_to_func_sig = {}

    if g_src_map:  # not bytecode
        results = {
            'evm_code_coverage': '',
            'vulnerabilities': {
                'reentrancy': [],
                'assertion_failure': [],
            }
        }
    else:# bytecode,hen duo False,not []
        results = {
            'evm_code_coverage': '',
            'vulnerabilities': {
                'reentrancy': False,
            }
        }

    global calls_affect_state
    calls_affect_state = {}

    global params_backup    #   backup params
    params_backup = {}

    global storage_backup
    storage_backup = {}

    global storage_dict_kv  # 在new_path中出现过的
    storage_dict_kv = {}

    global unsafecall_affect_list
    unsafecall_affect_list = []

    global call_result_list  # 记录当前路径call结果
    call_result_list = []

    global function_sig_list
    function_sig_list = []

    global sr_result
    sr_result = []

    global function_sig_address
    function_sig_address = {}

    # capturing the last statement of each basic block
    global end_ins_dict
    end_ins_dict = {}

    # capturing all the instructions, keys are corresponding addresses
    global instructions
    instructions = {}

    # capturing the "jump type" of each basic block
    global jump_type
    jump_type = {}

    global vertices
    vertices = {}

    global edges
    edges = {}

    global visited_edges
    visited_edges = {}

    global reentrancy_all_paths
    reentrancy_all_paths = []

    # store the path condition corresponding to each path in money_flow_all_paths
    global path_conditions
    path_conditions = []

    # store problem pc
    global global_problematic_pcs
    global_problematic_pcs = {"reentrancy_bug": [], "assertion_failure": []}

    global total_no_of_paths
    total_no_of_paths = 0

    global no_of_test_cases
    no_of_test_cases = 0

    # to generate names for symbolic variables
    global gen
    gen = Generator()

    global data_source
    if global_params.USE_GLOBAL_BLOCKCHAIN:
        data_source = EthereumData()

    # report file
    global rfile
    if global_params.REPORT_MODE:
        rfile = open(g_disasm_file + '.report', 'w')

def is_testing_evm():
    return global_params.UNIT_TEST != 0

def compare_storage_and_gas_unit_test(global_state, analysis):
    unit_test = pickle.load(open(PICKLE_PATH, 'rb'))
    test_status = unit_test.compare_with_symExec_result(global_state, analysis)
    exit(test_status)

def change_format():
    with open(g_disasm_file) as disasm_file:
        file_contents = disasm_file.readlines()
        i = 0
        firstLine = file_contents[0].strip('\n')
        # print(file_contents)
        for line in file_contents:
            line = line.replace('SELFDESTRUCT', 'SUICIDE')
            line = line.replace('Missing opcode 0xfd', 'REVERT')
            line = line.replace('Missing opcode 0xfe', 'ASSERTFAIL')
            line = re.sub(r'Missing opcode .{3,4}', 'INVALID', line) #Missing opcode 0x?? -> invalid
            line = line.replace(':', '')
            lineParts = line.split(' ')
            try: # removing initial zeroes
                lineParts[0] = str(int(lineParts[0]))

            except:
                lineParts[0] = lineParts[0]
            lineParts[-1] = lineParts[-1].strip('\n')
            # print("lineparts[-1]",lineParts[-1])
            try: # adding arrow if last is a number
                lastInt = lineParts[-1]
                if(int(lastInt, 16) or int(lastInt, 16) == 0) and len(lineParts) > 2:
                    lineParts[-1] = "=>"
                    lineParts.append(lastInt) # operator => number
            except Exception:
                pass
            file_contents[i] = ' '.join(lineParts)
            # print(file_contents[i])
            i = i + 1
        file_contents[0] = firstLine
        file_contents[-1] += '\n'

    with open(g_disasm_file, 'w') as disasm_file:
        disasm_file.write("\n".join(file_contents)) # contents write in .disasm file

def build_cfg_and_analyze():
    change_format()
    with open(g_disasm_file, 'r') as disasm_file:
        disasm_file.readline()  # Remove first line
        tokens = tokenize.generate_tokens(disasm_file.readline) # return iterator
        collect_vertices(tokens)
        construct_bb()
        construct_static_edges()
        full_sym_exec()  # jump targets are constructed on the fly


def print_cfg():
    for block in vertices.values():
        block.display()
    log.debug(str(edges))

'''mapping source and instruction?'''
def mapping_push_instruction(current_line_content, current_ins_address, idx, positions, length):
    global g_src_map

    while (idx < length):
        if not positions[idx]:
            return idx + 1
        name = positions[idx]['name']
        if name.startswith("tag"):
            idx += 1
        else:
            if name.startswith("PUSH"):
                if name == "PUSH":
                    value = positions[idx]['value']
                    instr_value = current_line_content.split(" ")[1]
                    if int(value, 16) == int(instr_value, 16):
                        g_src_map.instr_positions[current_ins_address] = g_src_map.positions[idx]
                        idx += 1
                        break
                    else:
                        raise Exception("Source map error")
                else:
                    g_src_map.instr_positions[current_ins_address] = g_src_map.positions[idx]
                    idx += 1
                    break
            else:
                raise Exception("Source map error")
    return idx

def mapping_non_push_instruction(current_line_content, current_ins_address, idx, positions, length):
    global g_src_map

    while (idx < length):
        if not positions[idx]:
            return idx + 1
        name = positions[idx]['name']
        if name.startswith("tag"):
            idx += 1
        else:
            instr_name = current_line_content.split(" ")[0]
            if name == instr_name or name == "INVALID" and instr_name == "ASSERTFAIL" or name == "KECCAK256" and instr_name == "SHA3" or name == "SELFDESTRUCT" and instr_name == "SUICIDE":
                g_src_map.instr_positions[current_ins_address] = g_src_map.positions[idx]
                idx += 1
                break
            else:
                raise Exception("Source map error")
    return idx

# 1. Parse the disassembled file
# 2. Then identify each basic block (i.e. one-in, one-out)
# 3. Store them in vertices
def collect_vertices(tokens):
    global g_src_map
    if g_src_map:
        idx = 0
        positions = g_src_map.positions
        length = len(positions)
    global end_ins_dict
    global instructions
    global jump_type

    current_ins_address = 0
    last_ins_address = 0
    is_new_line = True
    current_block = 0 # block start address
    current_line_content = ""
    wait_for_push = False
    is_new_block = False

    for tok_type, tok_string, (srow, scol), _, line_number in tokens:
        if wait_for_push is True: # add value, to 16 jin zhi
            push_val = ""
            for ptok_type, ptok_string, _, _, _ in tokens:
                if ptok_type == NEWLINE:
                    is_new_line = True
                    current_line_content += push_val + ' '
                    # print("currentlinecontent:",current_line_content) # pushx 0xxx
                    instructions[current_ins_address] = current_line_content
                    idx = mapping_push_instruction(current_line_content, current_ins_address, idx, positions, length) if g_src_map else None
                    log.debug(current_line_content)
                    current_line_content = ""
                    wait_for_push = False
                    break
                try:
                    int(ptok_string, 16)
                    push_val += ptok_string
                except ValueError:
                    pass

            continue
        elif is_new_line is True and tok_type == NUMBER:  # looking for a line number
            last_ins_address = current_ins_address
            try:
                current_ins_address = int(tok_string) # line number(address)
            except ValueError:
                log.critical("ERROR when parsing row %d col %d", srow, scol)
                quit()
            is_new_line = False
            if is_new_block:
                current_block = current_ins_address # block start address
                is_new_block = False
            continue
        elif tok_type == NEWLINE:
            is_new_line = True
            log.debug(current_line_content)
            # print("current_line_content:",current_line_content)
            instructions[current_ins_address] = current_line_content # just operator
            idx = mapping_non_push_instruction(current_line_content, current_ins_address, idx, positions, length) if g_src_map else None
            current_line_content = ""
            continue
        elif tok_type == NAME: # just operator
            if tok_string == "JUMPDEST":
                if last_ins_address not in end_ins_dict:
                    end_ins_dict[current_block] = last_ins_address # before?? JUMPDEST address
                current_block = current_ins_address # JUMPDEST address
                is_new_block = False
            elif tok_string == "STOP" or tok_string == "RETURN" or tok_string == "SUICIDE" or tok_string == "REVERT" or tok_string == "ASSERTFAIL":
                jump_type[current_block] = "terminal"
                end_ins_dict[current_block] = current_ins_address
            elif tok_string == "JUMP":
                jump_type[current_block] = "unconditional"
                end_ins_dict[current_block] = current_ins_address
                is_new_block = True
            elif tok_string == "JUMPI":
                jump_type[current_block] = "conditional"
                end_ins_dict[current_block] = current_ins_address
                is_new_block = True
            elif tok_string == "CALL":
                jump_type[current_block] = "call_type"
                end_ins_dict[current_block] = current_ins_address
                is_new_block = True
            elif tok_string.startswith('PUSH', 0):
                wait_for_push = True
            is_new_line = False
        if tok_string != "=" and tok_string != ">":
            current_line_content += tok_string + " "

    '''????do nothing?what to do?'''
    if current_block not in end_ins_dict:
        log.debug("current block: %d", current_block)
        log.debug("last line: %d", current_ins_address)
        # print("current_block:",current_block)
        # print("current_ins_address:",current_ins_address)
        end_ins_dict[current_block] = current_ins_address

    '''not defined in jumptype, then default = terminal'''
    if current_block not in jump_type:
        jump_type[current_block] = "terminal"

    '''end block dont have type, default = falls_to'''
    for key in end_ins_dict:
        if key not in jump_type:
            jump_type[key] = "falls_to"

    # for k in instructions.keys():
    #     print("k:", k, "v:", instructions[k])
    # for key in end_ins_dict:
    #     print("end_ins_k:", key,"end_ins_v:",end_ins_dict[key])
    #     print("jump_type:",jump_type[key])

def construct_bb():
    global vertices # key:begin address, value: BasicBlock(begin,end)
    global edges
    sorted_addresses = sorted(instructions.keys()) # sorted operator instruction address
    size = len(sorted_addresses)
    for key in end_ins_dict:
        end_address = end_ins_dict[key]
        block = BasicBlock(key, end_address) # begin address, end address
        # print("key:",key,"end_add:",end_address)
        if key not in instructions:
            continue
        block.add_instruction(instructions[key]) # begin instruction
        # print("ins[key]",instructions[key])
        i = sorted_addresses.index(key) + 1
        while i < size and sorted_addresses[i] <= end_address:
            block.add_instruction(instructions[sorted_addresses[i]]) # add instructions to block
            # print("ins:",instructions[sorted_addresses[i]])
            i += 1
        block.set_block_type(jump_type[key])
        vertices[key] = block
        edges[key] = []


def construct_static_edges():
    add_falls_to()  # these edges are static


def add_falls_to():
    global vertices
    global edges
    key_list = sorted(jump_type.keys())
    length = len(key_list)
    for i, key in enumerate(key_list):
        if jump_type[key] != "terminal" and jump_type[key] != "unconditional" and i+1 < length:
            target = key_list[i+1]
            edges[key].append(target)
            vertices[key].set_falls_to(target) # key:begin address, target: next begin address
            # print("key:",key,"falls:",target)


def get_init_global_state(path_conditions_and_vars):
    global_state = {"balance": {}, "pc": 0}
    init_is = init_ia = deposited_value = sender_address = receiver_address = gas_price = origin = currentCoinbase = currentNumber = currentDifficulty = currentGasLimit = callData = None

    if global_params.INPUT_STATE:
        with open('state.json') as f:
            state = json.loads(f.read())
            if state["Is"]["balance"]:
                init_is = int(state["Is"]["balance"], 16)
            if state["Ia"]["balance"]:
                init_ia = int(state["Ia"]["balance"], 16)
            if state["exec"]["value"]:
                deposited_value = 0
            if state["Is"]["address"]:
                sender_address = int(state["Is"]["address"], 16)
            if state["Ia"]["address"]:
                receiver_address = int(state["Ia"]["address"], 16)
            if state["exec"]["gasPrice"]:
                gas_price = int(state["exec"]["gasPrice"], 16)
            if state["exec"]["origin"]:
                origin = int(state["exec"]["origin"], 16)
            if state["env"]["currentCoinbase"]:
                currentCoinbase = int(state["env"]["currentCoinbase"], 16)
            if state["env"]["currentNumber"]:
                currentNumber = int(state["env"]["currentNumber"], 16)
            if state["env"]["currentDifficulty"]:
                currentDifficulty = int(state["env"]["currentDifficulty"], 16)
            if state["env"]["currentGasLimit"]:
                currentGasLimit = int(state["env"]["currentGasLimit"], 16)

    # for some weird reason these 3 vars are stored in path_conditions insteaad of global_state
    else:
        sender_address = Symbol("Is", BVType(256))
        receiver_address = Symbol("Ia", BVType(256))
        deposited_value = Symbol("Iv", BVType(256))
        init_is = Symbol("init_Is", BVType(256))
        init_ia = Symbol("init_Ia", BVType(256))

    path_conditions_and_vars["Is"] = sender_address
    path_conditions_and_vars["Ia"] = receiver_address
    path_conditions_and_vars["Iv"] = deposited_value

    constraint = BVSGE(deposited_value, BVZero(256))
    path_conditions_and_vars["path_condition"].append(constraint)
    constraint = BVSGE(init_is, deposited_value)
    path_conditions_and_vars["path_condition"].append(constraint)
    constraint = BVSGE(init_ia, BVZero(256))
    path_conditions_and_vars["path_condition"].append(constraint)

    # update the balances of the "caller" and "callee"

    global_state["balance"]["Is"] = BVSub(init_is, deposited_value)
    global_state["balance"]["Ia"] = BVAdd(init_ia, deposited_value)

    if not gas_price:
        new_var_name = gen.gen_gas_price_var()
        gas_price = Symbol(new_var_name, BVType(256))
        path_conditions_and_vars[new_var_name] = gas_price

    if not origin:
        new_var_name = gen.gen_origin_var()
        origin = Symbol(new_var_name, BVType(256))
        path_conditions_and_vars[new_var_name] = origin

    if not currentCoinbase:
        new_var_name = "IH_c"
        currentCoinbase = Symbol(new_var_name, BVType(256))
        path_conditions_and_vars[new_var_name] = currentCoinbase

    if not currentNumber:
        new_var_name = "IH_i"
        currentNumber = Symbol(new_var_name, BVType(256))
        path_conditions_and_vars[new_var_name] = currentNumber

    if not currentDifficulty:
        new_var_name = "IH_d"
        currentDifficulty = Symbol(new_var_name, BVType(256))
        path_conditions_and_vars[new_var_name] = currentDifficulty

    if not currentGasLimit:
        new_var_name = "IH_l"
        currentGasLimit = Symbol(new_var_name, BVType(256))
        path_conditions_and_vars[new_var_name] = currentGasLimit

    new_var_name = "IH_s"
    currentTimestamp = Symbol(new_var_name, BVType(256))
    path_conditions_and_vars[new_var_name] = currentTimestamp

    # the state of the current current contract
    if "Ia" not in global_state:
        global_state["Ia"] = {}
    global_state["miu_i"] = 0
    global_state["value"] = deposited_value
    global_state["sender_address"] = sender_address
    global_state["receiver_address"] = receiver_address
    global_state["gas_price"] = gas_price
    global_state["origin"] = origin
    global_state["currentCoinbase"] = currentCoinbase
    global_state["currentTimestamp"] = currentTimestamp
    global_state["currentNumber"] = currentNumber
    global_state["currentDifficulty"] = currentDifficulty
    global_state["currentGasLimit"] = currentGasLimit

    return global_state

def get_start_block_to_func_sig():
    state = 0
    func_sig = None
    for pc, instr in six.iteritems(instructions):
        if state == 0 and instr.startswith('PUSH4'):
            state += 1
            func_sig = instr.split(' ')[1][2:]
        elif state == 1 and instr.startswith('EQ'):
            state += 1
        elif state == 2 and instr.startswith('PUSH'):
            state = 0
            pc = instr.split(' ')[1]
            pc = int(pc, 16)
            start_block_to_func_sig[pc] = func_sig  # pc:address, value:sig
            # print("pc:",pc,"sig:",func_sig)
        else:
            state = 0
    return start_block_to_func_sig

def full_sym_exec():
    global function_sig_address
    global function_sig_list
    # global call_target

    # executing, starting from beginning
    path_conditions_and_vars = {"path_condition": []}
    # print(g_src_map)
    global_state = get_init_global_state(path_conditions_and_vars)  # global state
    analysis = init_analysis()  # dict
    params = Parameter(path_conditions_and_vars=path_conditions_and_vars, global_state=global_state,
                       analysis=analysis, new_path_conditions_and_vars=path_conditions_and_vars)  # set attribution
    # params.new_path_conditions_and_vars = params.path_conditions_and_vars  # maybe no use, yifangwanyi
    # if g_src_map:
    function_sig_address = get_start_block_to_func_sig()  # get function signature(key:pc address, value:signature value)
    # print(function_sig_address)
    function_sig_list = list(function_sig_address.keys())
    # print(function_sig_address.keys())
    if function_sig_list:
        Global_Flags.call_target = function_sig_list[0]
    else:
        Global_Flags.call_target = 0
    params.current_flow.append(0)
    return sym_exec_block(params, 0, 0, 0, -1, 'fallback')


# Symbolically executing a block from the start address
def sym_exec_block(params, block, pre_block, depth, func_call, current_func_name):
    global solver
    global visited_edges
    # global money_flow_all_paths
    global path_conditions
    global global_problematic_pcs
    global results
    global g_src_map
    global function_sig_address
    global function_sig_list
    global storage_dict_kv
    global call_result_list
    global params_backup
    global unsafecall_affect_list
    global sr_result

    visited = params.visited
    stack = params.stack
    mem = params.mem
    memory = params.memory
    global_state = params.global_state
    sha3_list = params.sha3_list
    path_conditions_and_vars = params.path_conditions_and_vars
    new_path_conditions_and_vars = params.new_path_conditions_and_vars
    analysis = params.analysis
    calls = params.calls
    current_flow = params.current_flow
    reentry_key_pcs = params.reentry_key_pcs
    current_function = params.current_function
    in_call_flow = params.in_call_flow
    out_call_flow = params.out_call_flow
    been_call = params.been_call
    # overflow_pcs = params.overflow_pcs

    Edge = namedtuple("Edge", ["v1", "v2"])  # Factory Function for tuples is used as dictionary key
    if block < 0:  # jump address, start address
        log.debug("UNKNOWN JUMP ADDRESS. TERMINATING THIS PATH")
        return ["ERROR"]

    log.debug("Reach block address %d \n", block)

    if g_src_map:
        if block in function_sig_address:  # function address
            func_sig = function_sig_address[block]  # set signature
            current_func_name = g_src_map.sig_to_func[func_sig]  # set function name
            # print("current_func_name:", current_func_name)  # func_name(xxx)
            pattern = r'(\w[\w\d_]*)\((.*)\)$'
            match = re.match(pattern, current_func_name)
            if match:
                current_func_name = list(match.groups())[0]  # just func_name
                # print("current_func_name:",current_func_name)

    current_edge = Edge(pre_block, block)
    if current_edge in visited_edges:
        updated_count_number = visited_edges[current_edge] + 1
        visited_edges.update({current_edge: updated_count_number})  # visited count number
    else:
        visited_edges.update({current_edge: 1})  # visited count number

    if visited_edges[current_edge] > global_params.LOOP_LIMIT:
        log.debug("Overcome a number of loop limit. Terminating this path ...")
        return stack

    current_gas_used = analysis["gas"]
    if current_gas_used > global_params.GAS_LIMIT:
        log.debug("Run out of gas. Terminating this path ... ")
        return stack

    # Execute every instruction, one at a time
    try:
        block_ins = vertices[block].get_instructions()
    except KeyError:
        log.debug("This path results in an exception, possibly an invalid jump address")
        return ["ERROR"]

    for instr in block_ins:
        sym_exec_ins(params, block, depth, instr, func_call, current_func_name)

    # Mark that this basic block in the visited blocks
    visited.append(block)
    depth += 1

    reentrancy_all_paths.append(analysis["reentrancy_bug"])

    # Go to next Basic Block(s)
    if jump_type[block] == "terminal" or depth > global_params.DEPTH_LIMIT:
        global total_no_of_paths
        global no_of_test_cases

        total_no_of_paths += 1

        if global_params.GENERATE_TEST_CASES:
            try:
                model = solver.get_model()
                no_of_test_cases += 1
                filename = "test%s.otest" % no_of_test_cases
                with open(filename, 'w') as f:
                    for variable in model.environment.formula_manager.get_all_symbols():
                        f.write(str(variable) + " = " + str(model.get_value(variable)) + "\n")
                if os.stat(filename).st_size == 0:
                    os.remove(filename)
                    no_of_test_cases -= 1
            except Exception as e:
                pass

        # log.debug("TERMINATING A PATH ...")
        # display_analysis(analysis)
        if is_testing_evm():
            compare_storage_and_gas_unit_test(global_state, analysis)

    elif jump_type[block] == "unconditional":  # executing "JUMP"
        successor = vertices[block].get_jump_target()
        new_params = params.copy()
        new_params.global_state["pc"] = successor
        new_params.current_flow.append(successor)
        if isUnlockVar(Global_Flags.call_flag):  # 不在call途中
            if isLockVar(been_call):
                new_params.out_call_flow.append(successor)
            if function_sig_list:
                if successor in function_sig_list:
                    new_params.current_function.append(successor)
        else:
            new_params.in_call_flow.append(successor)
        if g_src_map:
            source_code = g_src_map.get_source_code(global_state['pc'])
            if source_code in g_src_map.func_call_names:
                func_call = global_state['pc']
        sym_exec_block(new_params, successor, block, depth, func_call, current_func_name)
    elif jump_type[block] == "falls_to":  # just follow to the next basic block
        successor = vertices[block].get_falls_to()
        new_params = params.copy()
        new_params.global_state["pc"] = successor
        new_params.current_flow.append(successor)
        if isUnlockVar(Global_Flags.call_flag):  # 不在call途中
            if isLockVar(been_call):
                new_params.out_call_flow.append(successor)
            if function_sig_list:
                if successor in function_sig_list:
                    new_params.current_function.append(successor)
        else:
            new_params.in_call_flow.append(successor)
        sym_exec_block(new_params, successor, block, depth, func_call, current_func_name)
    elif jump_type[block] == "conditional":  # executing "JUMPI"

        # A choice point, we proceed with depth first search

        branch_expression = vertices[block].get_branch_expression()
        if branch_expression == None:
            branch_expression = Bool(True)
        log.debug("Branch expression: " + str(branch_expression))

        solver.push()  # SET A BOUNDARY FOR SOLVER
        solver.add_assertion(branch_expression)

        try:
            with Timeout(sec=global_params.TIMEOUT):
                ret = solver.solve()
            if not ret:  # unsat
                log.debug("INFEASIBLE PATH DETECTED")
            else:
                left_branch = vertices[block].get_jump_target()
                new_params = params.copy()
                new_params.global_state["pc"] = left_branch
                new_params.path_conditions_and_vars["path_condition"].append(branch_expression)
                if isLockVar(Global_Flags.call_flag): #in call
                    new_params.new_path_conditions_and_vars["path_condition"].append(branch_expression)
                last_idx = len(new_params.path_conditions_and_vars["path_condition"]) - 1
                # new_params.analysis["time_dependency_bug"][last_idx] = global_state["pc"]
                new_params.current_flow.append(left_branch)
                if isUnlockVar(Global_Flags.call_flag):  # 不在call途中
                    if isLockVar(been_call):
                        new_params.out_call_flow.append(left_branch)
                    if function_sig_list:
                        if left_branch in function_sig_list:
                            new_params.current_function.append(left_branch)
                else:
                    new_params.in_call_flow.append(left_branch)
                sym_exec_block(new_params, left_branch, block, depth, func_call, current_func_name)
        except TimeoutError:
            raise
        except Exception as e:
            # traceback.print_exc()
            if global_params.DEBUG_MODE:
                traceback.print_exc()

        solver.pop()  # POP SOLVER CONTEXT

        solver.push()  # SET A BOUNDARY FOR SOLVER
        negated_branch_expression = Not(branch_expression)
        solver.add_assertion(negated_branch_expression)

        log.debug("Negated branch expression: " + str(negated_branch_expression))

        try:
            with Timeout(sec=global_params.TIMEOUT):
                ret = solver.solve()
            if not ret:  # unsat
                # Note that this check can be optimized. I.e. if the previous check succeeds,
                # no need to check for the negated condition, but we can immediately go into
                # the else branch
                log.debug("INFEASIBLE PATH DETECTED")
            else:
                right_branch = vertices[block].get_falls_to()
                new_params = params.copy()
                new_params.global_state["pc"] = right_branch
                new_params.path_conditions_and_vars["path_condition"].append(negated_branch_expression)
                if isLockVar(Global_Flags.call_flag): #in call
                    new_params.new_path_conditions_and_vars["path_condition"].append(negated_branch_expression)
                last_idx = len(new_params.path_conditions_and_vars["path_condition"]) - 1
                # new_params.analysis["time_dependency_bug"][last_idx] = global_state["pc"]
                new_params.current_flow.append(right_branch)
                if isUnlockVar(Global_Flags.call_flag):  # 不在call途中
                    if isLockVar(been_call):
                        new_params.out_call_flow.append(right_branch)
                    if function_sig_list:
                        if right_branch in function_sig_list:
                            new_params.current_function.append(right_branch)
                else:
                    new_params.in_call_flow.append(right_branch)
                sym_exec_block(new_params, right_branch, block, depth, func_call, current_func_name)
        except TimeoutError:
            raise
        except Exception as e:
            # traceback.print_exc()
            if global_params.DEBUG_MODE:
                traceback.print_exc()
        solver.pop()  # POP SOLVER CONTEXT
        updated_count_number = visited_edges[current_edge] - 1
        visited_edges.update({current_edge: updated_count_number})
    elif jump_type[block] == "call_type":
        successor = vertices[block].get_falls_to()
        if isUnlockVar(Global_Flags.call_flag):
            # 不在call途中
            for i in range(Global_Flags.path_index):  # 几个stop结果就几个顺序执行
                new_params = params_backup[block]
                new_params.global_state["pc"] = successor
                new_params.global_state["Ia"] = call_result_list[i]["storage"]
                new_params.sha3_list = call_result_list[i]["sha3_list"]
                new_params.current_flow = call_result_list[i]["current_flow"]
                new_params.in_call_flow = call_result_list[i]["in_call_flow"]
                new_params.reentry_key_pcs = call_result_list[i]["reentry_key_pcs"]
                new_params.current_flow.append(successor)
                if isLockVar(new_params.been_call):
                    new_params.out_call_flow.append(successor)
                sym_exec_block(new_params, successor, block, depth, func_call, current_func_name)  # go falls_to
            params.been_call = unlock_var(been_call)
        else:
            # 在call途中
            new_params = params.copy()
            new_params.global_state["pc"] = successor
            new_params.current_flow.append(successor)
            new_params.in_call_flow.append(successor)
            sym_exec_block(new_params, successor, block, depth, func_call, current_func_name)  # go falls_to

    else:
        updated_count_number = visited_edges[current_edge] - 1
        visited_edges.update({current_edge: updated_count_number})
        raise Exception('Unknown Jump-Type')


# Symbolically executing an instruction
def sym_exec_ins(params, block, depth, instr, func_call, current_func_name):
    global MSIZE
    global visited_pcs
    global solver
    global vertices
    global edges
    global g_src_map
    global calls_affect_state
    global data_source
    global function_sig_address
    global function_sig_list
    global params_backup
    global storage_backup
    global storage_dict_kv
    global call_result_list
    global unsafecall_affect_list
    global sr_result

    stack = params.stack
    mem = params.mem
    memory = params.memory
    global_state = params.global_state
    sha3_list = params.sha3_list
    path_conditions_and_vars = params.path_conditions_and_vars
    new_path_conditions_and_vars = params.new_path_conditions_and_vars
    analysis = params.analysis
    calls = params.calls
    current_flow = params.current_flow
    reentry_key_pcs = params.reentry_key_pcs
    current_function = params.current_function
    in_call_flow = params.in_call_flow
    out_call_flow = params.out_call_flow
    been_call = params.been_call

    visited_pcs.add(global_state["pc"])

    instr_parts = str.split(instr, ' ')
    opcode = instr_parts[0]

    if opcode == "INVALID":
        return
    elif opcode == "ASSERTFAIL":
        if g_src_map:
            source_code = g_src_map.get_source_code(global_state['pc'])
            source_code = source_code.split("(")[0]
            func_name = source_code.strip()
            model = None
            if check_sat(solver, False):
                model = solver.get_model()
            if func_name == "assert":  # shifou function assert
                global_problematic_pcs["assertion_failure"].append(Assertion(global_state["pc"], model))  # pc, model
            elif func_call != -1:
                global_problematic_pcs["assertion_failure"].append(Assertion(func_call, model))  # pc, model
        return

    # collecting the analysis result by calling this skeletal function
    # this should be done before symbolically executing the instruction,
    # since SE will modify the stack and mem
    # update_analysis(analysis, opcode, stack, mem, global_state, path_conditions_and_vars, solver)

    log.debug("==============================")
    log.debug("EXECUTING: " + instr)

    #
    #  0s: Stop and Arithmetic Operations
    #
    if opcode == "STOP":
        if isLockVar(Global_Flags.call_flag):  # 在call途中
            update_sr_postion(new_path_conditions_and_vars, global_state, storage_dict_kv, Global_Flags.path_index)
            if Global_Flags.call_target not in current_function:
                ret_v = check_dw_reentry(storage_backup, global_state['Ia'])
            else:
                ret_v = False
            # print("retv:",ret_v)
            if ret_v:
                analysis["reentrancy_bug"].append(True)
                global_problematic_pcs["reentrancy_bug"].append(reentry_key_pcs)
                # print('analysis:',analysis["reentrancy_bug"])
            # 记录当前路径结果call_result_list
            # print("path:", Global_Flags.path_index)
            call_result={}
            call_result["path_index"] = Global_Flags.path_index
            call_result["storage"] = global_state['Ia']
            call_result["current_flow"] = current_flow
            call_result["in_call_flow"] = in_call_flow
            call_result["reentry_key_pcs"] = reentry_key_pcs
            call_result["sha3_list"] = sha3_list
            call_result_list.append(call_result)
            # update path
            Global_Flags.path_index += 1
        else:
            validate_sr_reentry(analysis, global_problematic_pcs, out_call_flow, sr_result)

        global_state["pc"] = global_state["pc"] + 1
        return
    elif opcode == "ADD":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            # Type conversion is needed when they are mismatched
            if isReal(first) and isSymbolic(second):
                first = to_symbolic(first)
                computed = BVAdd(first, second).simplify()
            elif isSymbolic(first) and isReal(second):
                second = to_symbolic(second)
                computed = BVAdd(first, second).simplify()
            elif isAllReal(first, second):
                # both are real and we need to manually modulus with 2 ** 256
                computed = (first + second) % (2 ** 256)
            else:
                # if both are symbolic solver takes care of modulus automatically
                first = to_symbolic(first)
                second = to_symbolic(second)
                computed = BVAdd(first, second).simplify()

            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MUL":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isReal(first) and isSymbolic(second):
                first = to_symbolic(first)
                computed = BVMul(first, second).simplify()
            elif isSymbolic(first) and isReal(second):
                second = to_symbolic(second)
                computed = BVMul(first, second).simplify()
            elif isAllReal(first, second):
                computed = first * second & UNSIGNED_BOUND_NUMBER
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                computed = BVMul(first, second).simplify()
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SUB":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isReal(first) and isSymbolic(second):
                first = to_symbolic(first)
                computed = BVSub(first, second).simplify()
            elif isSymbolic(first) and isReal(second):
                second = to_symbolic(second)
                computed = BVSub(first, second).simplify()
            elif isAllReal(first, second):
                computed = (first - second) % (2 ** 256)
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                computed = BVSub(first, second).simplify()
            # computed = simplify(computed) if is_expr(computed) else computed

            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "DIV":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if second == 0:
                    computed = 0  # div 0 = 0
                else:
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    computed = first / second
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add_assertion(NotEquals(second, BVZero(256)))
                if not check_sat(solver):
                    computed = 0
                else:
                    computed = BVUDiv(first, second).simplify()
                solver.pop()
            # computed = computed.simplify() if isSymbolic(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SDIV":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_signed(first)
                second = to_signed(second)
                if second == 0:
                    computed = 0
                elif first == -2**255 and second == -1:
                    computed = -2**255
                else:
                    sign = -1 if (first / second) < 0 else 1
                    computed = sign * ( abs(first) / abs(second) )
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add_assertion(NotEquals(second, BVZero(256)))
                if not check_sat(solver):
                    computed = 0
                else:
                    solver.push()
                    # solver.add( Not( And(first == -2**255, second == -1 ) ))
                    solver.add_assertion(Not(And(Equals(first, BV(CONSTANT_MAX_NEG255, 256)), Equals(second, BV(CONSTANT_MAX_FF256, 256)))))
                    if not check_sat(solver):
                        # computed = -2**255
                        computed = CONSTANT_MAX_NEG255
                    else:
                        # solver.push()
                        # solver.add_assertion(BVSLT(BVSDiv(first, second), BVZero(256)))
                        # sign = -1 if check_sat(solver) is True else 1
                        # # z3_abs = lambda x: If(x >= 0, x, -x)
                        # first = BV_abs(first)
                        # second = BV_abs(second)
                        # computed = BVMul(SBV(sign, 256), BVUDiv(first, second))
                        # solver.pop()
                        computed = BVSDiv(first, second).simplify()
                    solver.pop()
                solver.pop()
            # computed = computed.simplify() if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MOD":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if second == 0:
                    computed = 0
                else:
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    computed = first % second & UNSIGNED_BOUND_NUMBER

            else:
                first = to_symbolic(first)
                second = to_symbolic(second)

                solver.push()
                solver.add_assertion(NotEquals(second, BVZero(256)))
                if not check_sat(solver):
                    # it is provable that second is indeed equal to zero
                    computed = 0
                else:
                    computed = BVURem(first, second).simplify()
                solver.pop()

            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SMOD":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if second == 0:
                    computed = 0
                else:
                    first = to_signed(first)
                    second = to_signed(second)
                    sign = -1 if first < 0 else 1
                    computed = sign * (abs(first) % abs(second))
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)

                solver.push()
                solver.add_assertion(NotEquals(second, BVZero(256)))
                if not check_sat(solver):
                    # it is provable that second is indeed equal to zero
                    computed = 0
                else:
                    # solver.push()
                    # solver.add(first < 0) # check sign of first element
                    # sign = BitVecVal(-1, 256) if check_sat(solver) == sat \
                    #     else BitVecVal(1, 256)
                    # solver.pop()
                    #
                    # z3_abs = lambda x: If(x >= 0, x, -x)
                    # first = z3_abs(first)
                    # second = z3_abs(second)
                    #
                    # computed = sign * (first % second)
                    computed = BVSRem(first, second).simplify()
                solver.pop()

            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "ADDMOD":
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            third = stack.pop(0)

            if isAllReal(first, second, third):
                if third == 0:
                    computed = 0
                else:
                    computed = (first + second) % third
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                third = to_symbolic(third)
                solver.push()
                solver.add_assertion(NotEquals(third, BVZero(256)))
                if not check_sat(solver):
                    computed = 0
                else:
                    first = BVZExt(first, 256)
                    second = BVZExt(second, 256)
                    third = BVZExt(third, 256)
                    computed = BVURem(BVAdd(first, second), third)
                    computed = BVExtract(computed, 0, 255).simplify()
                solver.pop()
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MULMOD":
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            third = stack.pop(0)

            if isAllReal(first, second, third):
                if third == 0:
                    computed = 0
                else:
                    computed = (first * second) % third
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                third = to_symbolic(third)
                solver.push()
                solver.add_assertion(NotEquals(third, BVZero(256)))
                if not check_sat(solver):
                    computed = 0
                else:
                    first = BVZExt(first, 256)
                    second = BVZExt(second, 256)
                    third = BVZExt(third, 256)
                    computed = BVURem(BVMul(first, second), third)
                    computed = BVExtract(computed, 0, 255).simplify()
                solver.pop()
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "EXP":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            base = stack.pop(0)
            exponent = stack.pop(0)
            # Type conversion is needed when they are mismatched
            if isAllReal(base, exponent):
                computed = pow(base, exponent, 2**256)
            else:
                # The computed value is unknown, this is because power is
                # not supported in bit-vector theory
                new_var_name = gen.gen_arbitrary_var()
                computed = Symbol(new_var_name, BVType(256)).simplify()
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SIGNEXTEND":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if first >= 32 or first < 0:
                    computed = second
                else:
                    signbit_index_from_right = 8 * first + 7
                    if second & (1 << signbit_index_from_right):
                        computed = second | (2 ** 256 - (1 << signbit_index_from_right))
                    else:
                        computed = second & ((1 << signbit_index_from_right) - 1 )
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add_assertion(Not(Or(BVSLE(32, first), BVSLT(first, 0))))
                # solver.add( Not( Or(first >= 32, first < 0 ) ) )
                if not check_sat(solver):
                    computed = second.simplify()
                else:
                    # signbit_index_from_right = 8 * first + 7
                    signbit_index_from_right = BVAdd(BVMul(BV(8, 256), first), BV(7, 256))
                    solver.push()
                    # solver.add(second & (1 << signbit_index_from_right) == 0)
                    solver.add_assertion(Equals(BVAnd(second, BVLShl(BV(1, 256), signbit_index_from_right)), BVZero(256)))
                    if not check_sat(solver):
                        # computed = second | (2 ** 256 - (1 << signbit_index_from_right))
                        computed = BVOr(second, BVNeg(BVLShl(BV(1, 256), signbit_index_from_right))).simplify()
                    else:
                        # computed = second & ((1 << signbit_index_from_right) - 1)
                        computed = BVAnd(second, BVSub(BVLShl(BV(1, 256), signbit_index_from_right), BV(1, 256))).simplify()
                    solver.pop()
                solver.pop()
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    #
    #  10s: Comparison and Bitwise Logic Operations
    #
    elif opcode == "LT":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_unsigned(first)
                second = to_unsigned(second)
                if first < second:
                    computed = 1
                else:
                    computed = 0
            else:
                # computed = If(ULT(first, second), BitVecVal(1, 256), BitVecVal(0, 256))
                computed = Ite(BVULT(to_symbolic(first), to_symbolic(second)), BV(1, 256), BV(0, 256)).simplify()
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "GT":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_unsigned(first)
                second = to_unsigned(second)
                if first > second:
                    computed = 1
                else:
                    computed = 0
            else:
                # computed = If(UGT(first, second), BitVecVal(1, 256), BitVecVal(0, 256))
                computed = Ite(BVUGT(to_symbolic(first), to_symbolic(second)), BV(1, 256), BV(0, 256)).simplify()
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SLT":  # Not fully faithful to signed comparison
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_signed(first)
                second = to_signed(second)
                if first < second:
                    computed = 1
                else:
                    computed = 0
            else:
                # computed = If(first < second, BitVecVal(1, 256), BitVecVal(0, 256))
                computed = Ite(BVSLT(to_symbolic(first), to_symbolic(second)), BV(1, 256), BV(0, 256)).simplify()
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SGT":  # Not fully faithful to signed comparison
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_signed(first)
                second = to_signed(second)
                if first > second:
                    computed = 1
                else:
                    computed = 0
            else:
                # computed = If(first > second, BitVecVal(1, 256), BitVecVal(0, 256))
                computed = Ite(BVSGT(to_symbolic(first), to_symbolic(second)), BV(1, 256), BV(0, 256)).simplify()
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "EQ":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if first == second:
                    computed = 1
                else:
                    computed = 0
            else:
                # computed = If(first == second, BitVecVal(1, 256), BitVecVal(0, 256))
                computed = Ite(Equals(to_symbolic(first), to_symbolic(second)), BV(1, 256), BV(0, 256)).simplify()
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "ISZERO":
        # Tricky: this instruction works on both boolean and integer,
        # when we have a symbolic expression, type error might occur
        # Currently handled by try and catch
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            if isReal(first):
                if first == 0:
                    computed = 1
                else:
                    computed = 0
            else:
                # computed = If(first == 0, BitVecVal(1, 256), BitVecVal(0, 256))
                if first.get_type() is types.BOOL:
                    computed = Ite(EqualsOrIff(first, Bool(False)), BV(1, 256), BV(0, 256)).simplify()
                else:
                    computed = Ite(EqualsOrIff(first, BVZero(256)), BV(1, 256), BV(0, 256)).simplify()
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "AND":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            computed = first & second
            computed = computed.simplify() if isSymbolic(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "OR":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)

            computed = first | second
            computed = computed.simplify() if isSymbolic(computed) else computed
            stack.insert(0, computed)

        else:
            raise ValueError('STACK underflow')
    elif opcode == "XOR":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)

            computed = first ^ second
            computed = computed.simplify() if isSymbolic(computed) else computed
            stack.insert(0, computed)

        else:
            raise ValueError('STACK underflow')
    elif opcode == "NOT":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            computed = (~first) & UNSIGNED_BOUND_NUMBER
            computed = computed.simplify() if isSymbolic(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "BYTE":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            byte_index = 32 - first - 1
            second = stack.pop(0)

            if isAllReal(first, second):
                if first >= 32 or first < 0:
                    computed = 0
                else:
                    computed = second & (255 << (8 * byte_index))
                    computed = computed >> (8 * byte_index)
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                # solver.add( Not (Or( first >= 32, first < 0 ) ) )
                solver.add_assertion(Not(Or(BVSGE(first, BV(32, 256)), BVSLT(first, BVZero(256)))))
                if not check_sat(solver):
                    computed = 0
                else:
                    byte_index = to_symbolic(byte_index)
                    # computed = second & (255 << (8 * byte_index))
                    computed = BVAnd(BV(second, 256), BVLShl(BV(255, 256), BVMul(BV(8, 256), BV(byte_index, 256))))
                    # computed = computed >> (8 * byte_index)
                    computed = BVAShr(computed, BVMul(BV(8, 256), BV(byte_index, 256)))
                solver.pop()
            computed = computed.simplify() if isSymbolic(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    #
    # 20s: SHA3
    #
    elif opcode == "SHA3":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            s0 = stack.pop(0)
            s1 = stack.pop(0)
            if isAllReal(s0, s1):
                # simulate the hashing of sha3
                data = [str(x) for x in memory[s0: s0 + s1]]
                position = ''.join(data)
                position = re.sub('[\s+]', '', position)
                position = zlib.compress(six.b(position), 9)
                position = base64.b64encode(position)
                position = position.decode('utf-8', 'strict')
                if position in sha3_list:
                    stack.insert(0, sha3_list[position])
                else:
                    new_var_name = gen.gen_arbitrary_var()
                    # new_var = BitVec(new_var_name, 256)
                    new_var = Symbol(new_var_name, BVType(256))
                    sha3_list[position] = new_var
                    stack.insert(0, new_var)
            else:
                # push into the execution a fresh symbolic variable
                new_var_name = gen.gen_arbitrary_var()
                new_var = Symbol(new_var_name, BVType(256))
                path_conditions_and_vars[new_var_name] = new_var
                stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    #
    # 30s: Environment Information
    #
    elif opcode == "ADDRESS":  # get address of currently executing account
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, path_conditions_and_vars["Ia"])
    elif opcode == "BALANCE":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            address = stack.pop(0)
            if isReal(address) and global_params.USE_GLOBAL_BLOCKCHAIN:
                new_var = data_source.getBalance(address)
            else:
                new_var_name = gen.gen_balance_var()
                if new_var_name in path_conditions_and_vars:
                    new_var = path_conditions_and_vars[new_var_name]
                else:
                    # new_var = BitVec(new_var_name, 256)
                    new_var = Symbol(new_var_name, BVType(256))
                    path_conditions_and_vars[new_var_name] = new_var
            if isReal(address):
                hashed_address = "concrete_address_" + str(address)
            else:
                hashed_address = str(address)
            global_state["balance"][hashed_address] = new_var
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CALLER":  # get caller address
        # that is directly responsible for this execution
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["sender_address"])
    elif opcode == "ORIGIN":  # get execution origination address
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["origin"])
    elif opcode == "CALLVALUE":  # get value of this transaction
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["value"])
    elif opcode == "CALLDATALOAD":  # from input data from environment
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            position = stack.pop(0)
            new_var_name = ""
            if g_src_map:
                source_code = g_src_map.get_source_code(global_state['pc'] - 1)
                if source_code.startswith("function") and isReal(position) and current_func_name in g_src_map.func_name_to_params:
                    params = g_src_map.func_name_to_params[current_func_name]
                    param_idx = (position - 4) // 32
                    for param in params:
                        if param_idx == param['position']:
                            new_var_name = param['name']
                            g_src_map.var_names.append(new_var_name)
                else:
                    new_var_name = gen.gen_data_var(position)
            else:
                new_var_name = gen.gen_data_var(position)
            if new_var_name in path_conditions_and_vars:
                new_var = path_conditions_and_vars[new_var_name]
            else:
                # new_var = BitVec(new_var_name, 256)
                new_var = Symbol(new_var_name, BVType(256))
                path_conditions_and_vars[new_var_name] = new_var
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CALLDATASIZE":
        global_state["pc"] = global_state["pc"] + 1
        new_var_name = gen.gen_data_size()
        if new_var_name in path_conditions_and_vars:
            new_var = path_conditions_and_vars[new_var_name]
        else:
            new_var = Symbol(new_var_name, BVType(256))
            path_conditions_and_vars[new_var_name] = new_var
        stack.insert(0, new_var)
    elif opcode == "CALLDATACOPY":  # Copy input data to memory
        #  TODO: Don't know how to simulate this yet
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CODESIZE":
        if g_disasm_file.endswith('.disasm'):
            evm_file_name = g_disasm_file[:-7]
        else:
            evm_file_name = g_disasm_file
        with open(evm_file_name, 'r') as evm_file:
            evm = evm_file.read()[:-1]
            code_size = len(evm)/2
            stack.insert(0, code_size)
    elif opcode == "CODECOPY":
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            mem_location = stack.pop(0)
            code_from = stack.pop(0)
            no_bytes = stack.pop(0)
            current_miu_i = global_state["miu_i"]

            if isAllReal(mem_location, current_miu_i, code_from, no_bytes):
                if six.PY2:
                    temp = long(math.ceil((mem_location + no_bytes) / float(32)))
                else:
                    temp = int(math.ceil((mem_location + no_bytes) / float(32)))

                if temp > current_miu_i:
                    current_miu_i = temp

                if g_disasm_file.endswith('.disasm'):
                    evm_file_name = g_disasm_file[:-7]
                else:
                    evm_file_name = g_disasm_file
                with open(evm_file_name, 'r') as evm_file:
                    evm = evm_file.read()[:-1]
                    start = code_from * 2
                    end = start + no_bytes * 2
                    code = evm[start: end]
                try:
                    mem[mem_location] = int(code, 16)
                except Exception as e:
                    raise
                    # raise ValueError('STACK underflow')
            else:
                new_var_name = gen.gen_code_var("Ia", code_from, no_bytes)
                if new_var_name in path_conditions_and_vars:
                    new_var = path_conditions_and_vars[new_var_name]
                else:
                    new_var = Symbol(new_var_name, BVType(256))
                    path_conditions_and_vars[new_var_name] = new_var
                if isAllReal(mem_location, no_bytes):
                    if six.PY2:
                        temp = long(math.ceil((mem_location + no_bytes) / float(32)))
                    else:
                        temp = int(math.ceil((mem_location + no_bytes) / float(32)))
                else:
                    temp = (BVUDiv((to_symbolic(mem_location) + to_symbolic(no_bytes)), BV(32, 256))) + 1
                current_miu_i = to_symbolic(current_miu_i)
                # expression = current_miu_i < temp
                temp = to_symbolic(temp)
                expression = BVSLT(current_miu_i, temp).simplify()
                solver.push()
                solver.add_assertion(expression)
                if MSIZE:
                    if check_sat(solver):
                        # current_miu_i = If(expression, temp, current_miu_i)
                        current_miu_i = Ite(expression, temp, current_miu_i)
                solver.pop()
                mem.clear() # very conservative
                mem[str(mem_location)] = new_var
            global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif opcode == "RETURNDATACOPY":
        if len(stack) > 2:
            global_state["pc"] += 1
            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "RETURNDATASIZE":
        global_state["pc"] += 1
        new_var_name = gen.gen_arbitrary_var()
        new_var = Symbol(new_var_name, BVType(256))
        stack.insert(0, new_var)
    elif opcode == "GASPRICE":
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["gas_price"])
    elif opcode == "EXTCODESIZE":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            address = stack.pop(0)
            if isReal(address) and global_params.USE_GLOBAL_BLOCKCHAIN:
                code = data_source.getCode(address)
                stack.insert(0, len(code)/2)
            else:
                #not handled yet
                new_var_name = gen.gen_code_size_var(address)
                if new_var_name in path_conditions_and_vars:
                    new_var = path_conditions_and_vars[new_var_name]
                else:
                    new_var = Symbol(new_var_name, BVType(256))
                    path_conditions_and_vars[new_var_name] = new_var
                stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "EXTCODECOPY":
        if len(stack) > 3:
            global_state["pc"] = global_state["pc"] + 1
            address = stack.pop(0)
            mem_location = stack.pop(0)
            code_from = stack.pop(0)
            no_bytes = stack.pop(0)
            current_miu_i = global_state["miu_i"]

            if isAllReal(address, mem_location, current_miu_i, code_from, no_bytes) and global_params.USE_GLOBAL_BLOCKCHAIN:
                if six.PY2:
                    temp = long(math.ceil((mem_location + no_bytes) / float(32)))
                else:
                    temp = int(math.ceil((mem_location + no_bytes) / float(32)))
                if temp > current_miu_i:
                    current_miu_i = temp

                evm = data_source.getCode(address)
                start = code_from * 2
                end = start + no_bytes * 2
                code = evm[start: end]
                mem[mem_location] = int(code, 16)
            else:
                new_var_name = gen.gen_code_var(address, code_from, no_bytes)
                if new_var_name in path_conditions_and_vars:
                    new_var = path_conditions_and_vars[new_var_name]
                else:
                    new_var = Symbol(new_var_name, BVType(256))
                    path_conditions_and_vars[new_var_name] = new_var
                if isAllReal(mem_location, no_bytes):
                    if six.PY2:
                        temp = long(math.ceil((mem_location + no_bytes) / float(32)))
                    else:
                        temp = int(math.ceil((mem_location + no_bytes) / float(32)))
                else:
                    temp = (BVUDiv((to_symbolic(mem_location) + to_symbolic(no_bytes)), BV(32, 256))) + 1
                current_miu_i = to_symbolic(current_miu_i)
                # expression = current_miu_i < temp
                temp = to_symbolic(temp)
                expression = BVSLT(current_miu_i, temp).simplify()
                solver.push()
                solver.add_assertion(expression)
                if MSIZE:
                    if check_sat(solver):
                        # current_miu_i = If(expression, temp, current_miu_i)
                        current_miu_i = Ite(expression, temp, current_miu_i)
                solver.pop()
                mem.clear() # very conservative
                mem[str(mem_location)] = new_var
            global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    #
    #  40s: Block Information
    #
    elif opcode == "BLOCKHASH":  # information from block header
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            stack.pop(0)
            new_var_name = "IH_blockhash"
            if new_var_name in path_conditions_and_vars:
                new_var = path_conditions_and_vars[new_var_name]
            else:
                new_var = Symbol(new_var_name, BVType(256))
                path_conditions_and_vars[new_var_name] = new_var
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "COINBASE":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentCoinbase"])
    elif opcode == "TIMESTAMP":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentTimestamp"])
    elif opcode == "NUMBER":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentNumber"])
    elif opcode == "DIFFICULTY":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentDifficulty"])
    elif opcode == "GASLIMIT":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentGasLimit"])
    #
    #  50s: Stack, Memory, Storage, and Flow Information
    #
    elif opcode == "POP":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            stack.pop(0)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MLOAD":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            address = stack.pop(0)
            current_miu_i = global_state["miu_i"]
            if isAllReal(address, current_miu_i) and address in mem:
                if six.PY2:
                    temp = long(math.ceil((address + 32) / float(32)))
                else:
                    temp = int(math.ceil((address + 32) / float(32)))
                if temp > current_miu_i:
                    current_miu_i = temp
                value = mem[address]
                stack.insert(0, value)
            else:
                if not isSymbolic(address):
                    if six.PY2:
                        temp = long(math.ceil((address + 32) / float(32)))
                    else:
                        temp = int(math.ceil((address + 32) / float(32)))
                else:
                    # temp = ((address + 31) / 32) + 1
                    temp = BVAdd(BVUDiv(BVAdd(address, BV(31, 256)), BV(32, 256)), BV(1, 256))
                current_miu_i = to_symbolic(current_miu_i)
                # expression = current_miu_i < temp
                temp = to_symbolic(temp)
                expression = BVSLT(current_miu_i, temp).simplify()
                solver.push()
                solver.add_assertion(expression)
                if MSIZE:
                    if check_sat(solver):
                        # this means that it is possibly that current_miu_i < temp
                        # current_miu_i = If(expression, temp, current_miu_i)
                        current_miu_i = Ite(expression, temp, current_miu_i)
                solver.pop()
                new_var_name = gen.gen_mem_var(address)
                if new_var_name in path_conditions_and_vars:
                    new_var = path_conditions_and_vars[new_var_name]
                else:
                    new_var = Symbol(new_var_name, BVType(256))
                    path_conditions_and_vars[new_var_name] = new_var
                stack.insert(0, new_var)
                if isReal(address):
                    mem[address] = new_var
                else:
                    mem[str(address)] = new_var
            global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MSTORE":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            stored_address = stack.pop(0)
            stored_value = stack.pop(0)
            current_miu_i = global_state["miu_i"]
            if isReal(stored_address):
                # preparing data for hashing later
                old_size = len(memory) // 32
                new_size = ceil32(stored_address + 32) // 32
                mem_extend = (new_size - old_size) * 32
                memory.extend([0] * mem_extend)
                value = stored_value
                for i in range(31, -1, -1):
                    memory[stored_address + i] = value % 256
                    value /= 256
            if isAllReal(stored_address, current_miu_i):
                if six.PY2:
                    temp = long(math.ceil((stored_address + 32) / float(32)))
                else:
                    temp = int(math.ceil((stored_address + 32) / float(32)))
                if temp > current_miu_i:
                    current_miu_i = temp
                mem[stored_address] = stored_value  # note that the stored_value could be symbolic
            else:
                if not isSymbolic(stored_address):
                    if six.PY2:
                        temp = long(math.ceil((stored_address + 32) / float(32)))
                    else:
                        temp = int(math.ceil((stored_address + 32) / float(32)))
                else:
                    # temp = ((stored_address + 31) / 32) + 1
                    temp = BVAdd(BVUDiv(BVAdd(stored_address, BV(31, 256)), BV(32, 256)), BV(1, 256))
                current_miu_i = to_symbolic(current_miu_i)
                # expression = current_miu_i < temp
                temp = to_symbolic(temp)
                expression = BVSLT(current_miu_i, temp).simplify()
                solver.push()
                solver.add_assertion(expression)
                if MSIZE:
                    if check_sat(solver):
                        # this means that it is possibly that current_miu_i < temp
                        # current_miu_i = If(expression, temp, current_miu_i)
                        current_miu_i = Ite(expression, temp, current_miu_i)
                solver.pop()
                mem.clear()  # very conservative
                mem[str(stored_address)] = stored_value
            global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MSTORE8":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            stored_address = stack.pop(0)
            temp_value = stack.pop(0)
            stored_value = temp_value % 256  # get the least byte
            current_miu_i = global_state["miu_i"]
            if isAllReal(stored_address, current_miu_i):
                if six.PY2:
                    temp = long(math.ceil((stored_address + 1) / float(32)))
                else:
                    temp = int(math.ceil((stored_address + 1) / float(32)))
                if temp > current_miu_i:
                    current_miu_i = temp
                mem[stored_address] = stored_value  # note that the stored_value could be symbolic
            else:
                if not isSymbolic(stored_address):
                    if six.PY2:
                        temp = long(math.ceil((stored_address + 32) / float(32)))
                    else:
                        temp = int(math.ceil((stored_address + 32) / float(32)))
                else:
                    # temp = ((stored_address + 31) / 32) + 1
                    temp = BVAdd(BVUDiv(BVAdd(stored_address, BV(31, 256)), BV(32, 256)), BV(1, 256))
                if isReal(current_miu_i):
                    current_miu_i = BV(current_miu_i, 256)
                # expression = current_miu_i < temp
                temp = to_symbolic(temp)
                expression = BVSLT(current_miu_i, temp).simplify()
                solver.push()
                solver.add_assertion(expression)
                if MSIZE:
                    if check_sat(solver):
                        # this means that it is possibly that current_miu_i < temp
                        # current_miu_i = If(expression, temp, current_miu_i)
                        current_miu_i = Ite(expression, temp, current_miu_i)
                solver.pop()
                mem.clear()  # very conservative
                mem[str(stored_address)] = stored_value
            global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SLOAD":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            position = stack.pop(0)
            if isReal(position) and position in global_state["Ia"]:
                value = global_state["Ia"][position]
                stack.insert(0, value)
            elif global_params.USE_GLOBAL_STORAGE and isReal(position) and position not in global_state["Ia"]:
                value = data_source.getStorageAt(position)
                global_state["Ia"][position] = value
                stack.insert(0, value)
            else:
                if str(position) in global_state["Ia"]:
                    value = global_state["Ia"][str(position)]
                    stack.insert(0, value)
                else:
                    if isSymbolic(position):
                        position = position.simplify()
                    if g_src_map:
                        new_var_name = g_src_map.get_source_code(global_state['pc'] - 1)
                        operators = '[-+*/%|&^!><=]'
                        new_var_name = re.compile(operators).split(new_var_name)[0].strip()
                        new_var_name = g_src_map.get_parameter_or_state_var(new_var_name)
                        if new_var_name:
                            new_var_name = gen.gen_owner_store_var(position, new_var_name)
                        else:
                            new_var_name = gen.gen_owner_store_var(position)
                    else:
                        new_var_name = gen.gen_owner_store_var(position)

                    if new_var_name in path_conditions_and_vars:
                        new_var = path_conditions_and_vars[new_var_name]
                    else:
                        new_var = Symbol(new_var_name, BVType(256))
                        path_conditions_and_vars[new_var_name] = new_var
                    stack.insert(0, new_var)
                    if isReal(position):
                        global_state["Ia"][position] = new_var
                    else:
                        global_state["Ia"][str(position)] = new_var
        else:
            raise ValueError('STACK underflow')

    elif opcode == "SSTORE":
        if len(stack) > 1:
            for call_pc in calls:
                calls_affect_state[call_pc] = True
            stored_address = stack.pop(0)
            stored_value = stack.pop(0)
            if isReal(stored_address):
                # note that the stored_value could be unknown
                global_state["Ia"][stored_address] = stored_value
            else:
                # note that the stored_value could be unknown
                global_state["Ia"][str(stored_address)] = stored_value
            if isUnlockVar(Global_Flags.call_flag): # 不在call途中
                check_sr_reentry(stored_address, call_result_list, out_call_flow, storage_dict_kv, global_state["pc"], reentry_key_pcs, sr_result)
            global_state["pc"] = global_state["pc"] + 1
        else:
            raise ValueError('STACK underflow')
        # print("analysis:", analysis["reentrancy_bug"])
    elif opcode == "JUMP":
        if len(stack) > 0:
            target_address = stack.pop(0)
            if isSymbolic(target_address):
                try:
                    target_address = BV_to_int(target_address)
                except:
                    raise TypeError("Target address must be an integer")
            vertices[block].set_jump_target(target_address)
            if target_address not in edges[block]:
                edges[block].append(target_address)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "JUMPI":
        # We need to prepare two branches
        if len(stack) > 1:
            target_address = stack.pop(0)
            if isSymbolic(target_address):
                try:
                    target_address = BV_to_int(target_address)
                except:
                    raise TypeError("Target address must be an integer")
            vertices[block].set_jump_target(target_address)
            flag = stack.pop(0)
            # branch_expression = (BitVecVal(0, 1) == BitVecVal(1, 1))
            branch_expression = None
            if isReal(flag):
                if flag != 0:
                    branch_expression = Bool(True)
            else:
                branch_expression = (NotEquals(to_symbolic(flag), BVZero(256)))
            vertices[block].set_branch_expression(branch_expression)
            if target_address not in edges[block]:
                edges[block].append(target_address)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "PC":
        stack.insert(0, global_state["pc"])
        global_state["pc"] = global_state["pc"] + 1
    elif opcode == "MSIZE":
        global_state["pc"] = global_state["pc"] + 1
        msize = 32 * global_state["miu_i"]
        stack.insert(0, msize)
    elif opcode == "GAS":
        # In general, we do not have this precisely. It depends on both
        # the initial gas and the amount has been depleted
        # we need o think about this in the future, in case precise gas
        # can be tracked
        global_state["pc"] = global_state["pc"] + 1
        new_var_name = gen.gen_gas_var()
        new_var = Symbol(new_var_name, BVType(256))
        path_conditions_and_vars[new_var_name] = new_var
        stack.insert(0, new_var)
    elif opcode == "JUMPDEST":
        # Literally do nothing
        global_state["pc"] = global_state["pc"] + 1
    #
    #  60s & 70s: Push Operations
    #
    elif opcode.startswith('PUSH', 0):  # this is a push instruction
        position = int(opcode[4:], 10)
        global_state["pc"] = global_state["pc"] + 1 + position
        pushed_value = int(instr_parts[1], 16)
        stack.insert(0, pushed_value)
        if global_params.UNIT_TEST == 3: # test evm symbolic
            stack[0] = BV(stack[0], 256)
    #
    #  80s: Duplication Operations
    #
    elif opcode.startswith("DUP", 0):
        global_state["pc"] = global_state["pc"] + 1
        position = int(opcode[3:], 10) - 1
        if len(stack) > position:
            duplicate = stack[position]
            stack.insert(0, duplicate)
        else:
            raise ValueError('STACK underflow')

    #
    #  90s: Swap Operations
    #
    elif opcode.startswith("SWAP", 0):
        global_state["pc"] = global_state["pc"] + 1
        position = int(opcode[4:], 10)
        if len(stack) > position:
            temp = stack[position]
            stack[position] = stack[0]
            stack[0] = temp
        else:
            raise ValueError('STACK underflow')

    #
    #  a0s: Logging Operations
    #
    elif opcode in ("LOG0", "LOG1", "LOG2", "LOG3", "LOG4"):
        global_state["pc"] = global_state["pc"] + 1
        # We do not simulate these log operations
        num_of_pops = 2 + int(opcode[3:])
        while num_of_pops > 0:
            stack.pop(0)
            num_of_pops -= 1

    #
    #  f0s: System Operations
    #
    elif opcode == "CREATE":
        if len(stack) > 2:
            global_state["pc"] += 1
            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
            new_var_name = gen.gen_arbitrary_var()
            new_var = Symbol(new_var_name, BVType(256))
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CALL":
        # TODO: Need to handle miu_i
        global flag_judge
        flag_judge = True
        if len(stack) > 6:
        #         storage_backup = custom_deepcopy(global_state["Ia"])
            calls.append(global_state["pc"])
            for call_pc in calls:
                if call_pc not in calls_affect_state:
                    calls_affect_state[call_pc] = False
            outgas = stack.pop(0)
            recipient = stack.pop(0)
            transfer_amount = stack.pop(0)
            start_data_input = stack.pop(0)
            size_data_input = stack.pop(0)
            start_data_output = stack.pop(0)
            size_data_ouput = stack.pop(0)
            # in the paper, it is shaky when the size of data output is
            # min of stack[6] and the | o |

            if isReal(transfer_amount):
                if transfer_amount == 0:
                    stack.insert(0, 1)
                    # add call judge here ----- means can not call
                    flag_judge = False
                    return

            # Let us ignore the call depth
            balance_ia = global_state["balance"]["Ia"]
            transfer_amount = to_symbolic(transfer_amount)
            balance_ia = to_symbolic(balance_ia)
            # is_enough_fund = (transfer_amount <= balance_ia)
            is_enough_fund = BVSLE(transfer_amount, balance_ia)
            solver.push()
            solver.add_assertion(is_enough_fund)
            # print("is_enough_fund:", is_enough_fund)
            # print("z3:",solver)

            # 只要不是unsat，就认为有解，避免timeout
            if not check_sat(solver):
                # this means not enough fund, thus the execution will result in exception
                solver.pop()
                stack.insert(0, 0)
                flag_judge = False
            else:
                # the execution is possibly okay
                stack.insert(0, 1)
                flag_judge = True
                solver.pop()
                solver.add_assertion(is_enough_fund)
                path_conditions_and_vars["path_condition"].append(is_enough_fund)
                # new_balance_ia = (balance_ia - transfer_amount)
                new_balance_ia = BVSub(balance_ia, transfer_amount)
                global_state["balance"]["Ia"] = new_balance_ia
                address_is = path_conditions_and_vars["Is"]
                address_is = to_symbolic(address_is & CONSTANT_ONES_159)
                boolean_expression = NotEquals(to_symbolic(recipient), address_is)
                solver.push()
                solver.add_assertion(boolean_expression)
                # print("transfer_amount:",transfer_amount,"balance_ia:",balance_ia)
                # print("boolean_expression:",boolean_expression)
                if not check_sat(solver):
                    solver.pop()
                    new_balance_is = (global_state["balance"]["Is"] + transfer_amount)
                    global_state["balance"]["Is"] = new_balance_is
                else:
                    solver.pop()
                    if isReal(recipient):
                        new_address_name = "concrete_address_" + str(recipient)
                    else:
                        new_address_name = gen.gen_arbitrary_address_var()
                    old_balance_name = gen.gen_arbitrary_var()
                    old_balance = Symbol(old_balance_name, BVType(256))
                    path_conditions_and_vars[old_balance_name] = old_balance
                    constraint = BVSGE(old_balance, BVZero(256))
                    solver.add_assertion(constraint)
                    path_conditions_and_vars["path_condition"].append(constraint)
                    new_balance = BVAdd(old_balance, transfer_amount)
                    global_state["balance"][new_address_name] = new_balance
            # call judge ---- means call success
            if flag_judge:
                unsafecall = analysis_call(path_conditions_and_vars, outgas)
                if unsafecall:   # is not safe call and call success
                    reentry_key_pcs.append(global_state["pc"])
                    if isUnlockVar(Global_Flags.call_flag):  # unlock就有跳转，否则没有跳转
                        Global_Flags.call_flag = lock_var(Global_Flags.call_flag)
                        if global_state["pc"] not in unsafecall_affect_list:
                            unsafecall_affect_list.append(global_state["pc"])
                        params.been_call = lock_var(been_call)
                        params_backup[block] = params.copy()  # global params backup
                        storage_backup = global_state["Ia"]  # storage backup
                        for func_addr in function_sig_list:
                            Global_Flags.call_target = func_addr
                            vertices[block].set_call_target(Global_Flags.call_target)
                            # successor = vertices[block].get_falls_to()
                            new_params = params.copy()
                            new_params.global_state["pc"] = Global_Flags.call_target
                            new_params.current_flow.append(Global_Flags.call_target)
                            new_params.in_call_flow.append(Global_Flags.call_target)
                            reentry_key_pcs.append(Global_Flags.call_target)
                            new_params.reentry_key_pcs = reentry_key_pcs
                            sym_exec_block(new_params, Global_Flags.call_target, block, depth, func_call, current_func_name)  # 跳转

                        Global_Flags.call_flag = unlock_var(Global_Flags.call_flag)
                    pass
            global_state["pc"] = global_state["pc"] + 1
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CALLCODE":
        # TODO: Need to handle miu_i
        if len(stack) > 6:
            calls.append(global_state["pc"])
            for call_pc in calls:
                if call_pc not in calls_affect_state:
                    calls_affect_state[call_pc] = False
            global_state["pc"] = global_state["pc"] + 1
            outgas = stack.pop(0)
            recipient = stack.pop(0) # this is not used as recipient
            if global_params.USE_GLOBAL_STORAGE:
                if isReal(recipient):
                    recipient = hex(recipient)
                    if recipient[-1] == "L":
                        recipient = recipient[:-1]
                    recipients.add(recipient)
                else:
                    recipients.add(None)

            transfer_amount = stack.pop(0)
            start_data_input = stack.pop(0)
            size_data_input = stack.pop(0)
            start_data_output = stack.pop(0)
            size_data_ouput = stack.pop(0)
            # in the paper, it is shaky when the size of data output is
            # min of stack[6] and the | o |

            if isReal(transfer_amount):
                if transfer_amount == 0:
                    stack.insert(0, 1)
                    return

            # Let us ignore the call depth
            balance_ia = global_state["balance"]["Ia"]
            transfer_amount = to_symbolic(transfer_amount)
            balance_ia = to_symbolic(balance_ia)
            # is_enough_fund = (transfer_amount <= balance_ia)
            is_enough_fund = BVSLE(transfer_amount, balance_ia)
            solver.push()
            solver.add_assertion(is_enough_fund)

            if not check_sat(solver):
                # this means not enough fund, thus the execution will result in exception
                solver.pop()
                stack.insert(0, 0)
            else:
                # the execution is possibly okay
                stack.insert(0, 1)
                solver.pop()
                solver.add_assertion(is_enough_fund)
                path_conditions_and_vars["path_condition"].append(is_enough_fund)
        else:
            raise ValueError('STACK underflow')
    elif opcode in ("DELEGATECALL", "STATICCALL"):
        if len(stack) > 5:
            global_state["pc"] += 1
            stack.pop(0)
            recipient = stack.pop(0)
            if global_params.USE_GLOBAL_STORAGE:
                if isReal(recipient):
                    recipient = hex(recipient)
                    if recipient[-1] == "L":
                        recipient = recipient[:-1]
                    recipients.add(recipient)
                else:
                    recipients.add(None)

            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
            new_var_name = gen.gen_arbitrary_var()
            new_var = Symbol(new_var_name, BVType(256))
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "RETURN":
        # TODO: Need to handle miu_i
        if len(stack) > 1:
            stack.pop(0)
            stack.pop(0)
            # TODO
            if isLockVar(Global_Flags.call_flag):  # 在call途中
                update_sr_postion(new_path_conditions_and_vars, global_state, storage_dict_kv, Global_Flags.path_index)
                # return忽略DW
                # 记录当前路径结果call_result_list
                # print("path:", Global_Flags.path_index)
                call_result = {}
                call_result["path_index"] = Global_Flags.path_index
                call_result["storage"] = global_state['Ia']
                call_result["current_flow"] = current_flow
                call_result["in_call_flow"] = in_call_flow
                call_result["reentry_key_pcs"] = reentry_key_pcs
                call_result["sha3_list"] = sha3_list
                call_result_list.append(call_result)
                # update path
                Global_Flags.path_index += 1
            else:
                validate_sr_reentry(analysis, global_problematic_pcs, out_call_flow, sr_result)
            pass
        else:
            raise ValueError('STACK underflow')
        return
    elif opcode == "REVERT":
        # TODO: Need to handle miu_i
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            stack.pop(0)
            stack.pop(0)
            # TODO
            pass
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SUICIDE":
        global_state["pc"] = global_state["pc"] + 1
        recipient = stack.pop(0)
        transfer_amount = global_state["balance"]["Ia"]
        global_state["balance"]["Ia"] = 0
        if isReal(recipient):
            new_address_name = "concrete_address_" + str(recipient)
        else:
            new_address_name = gen.gen_arbitrary_address_var()
        old_balance_name = gen.gen_arbitrary_var()
        old_balance = Symbol(old_balance_name, BVType(256))
        path_conditions_and_vars[old_balance_name] = old_balance
        constraint = BVSGE(old_balance, BVZero(256))
        solver.add_assertion(constraint)
        path_conditions_and_vars["path_condition"].append(constraint)
        new_balance = BVAdd(old_balance, to_symbolic(transfer_amount))
        global_state["balance"][new_address_name] = new_balance
        # TODO
        return

    else:
        log.debug("UNKNOWN INSTRUCTION: " + opcode)
        if global_params.UNIT_TEST == 2 or global_params.UNIT_TEST == 3:
            log.critical("Unknown instruction: %s" % opcode)
            exit(UNKNOWN_INSTRUCTION)
        raise Exception('UNKNOWN INSTRUCTION: ' + opcode)


def detect_reentrancy():
    global g_src_map
    global results
    global reentrancy

    # print("rb:",global_problematic_pcs["reentrancy_bug"])
    final_p = extract_list_max(global_problematic_pcs["reentrancy_bug"])
    # print("fp:", final_p)
    for list_path in final_p:
        pcs = list_path
        reentrancy = Reentrancy(g_src_map, pcs)

        if g_src_map:
            results['vulnerabilities']['reentrancy'] = reentrancy.get_warnings()
        else:
            results['vulnerabilities']['reentrancy'] = reentrancy.is_vulnerable()
        log.info("\t  Re-Entrancy Vulnerability: \t %s", reentrancy.is_vulnerable())


def detect_assertion_failure():
    global g_src_map
    global results
    global assertion_failure

    assertion_failure = AssertionFailure(g_src_map, global_problematic_pcs['assertion_failure'])

    results['vulnerabilities']['assertion_failure'] = assertion_failure.get_warnings()
    s = "\t  Assertion Failure: \t\t\t %s" % assertion_failure.is_vulnerable()
    log.info(s)

def detect_vulnerabilities():
    global results
    global g_src_map
    global visited_pcs
    global global_problematic_pcs
    global begin
    global reentrancy

    reentrancy = None
    stop = time.time()
    dtime = stop - begin
    # print("ins:",instructions)
    log.info("\t  During time in Seconds: \t\t %f" % dtime)
    if instructions:
        evm_code_coverage = float(len(visited_pcs)) / len(instructions.keys()) * 100
        log.info("\t  EVM Code Coverage: \t\t\t %s%%", round(evm_code_coverage, 1))
        results["evm_code_coverage"] = str(round(evm_code_coverage, 1))


        # log.debug("Checking for Callstack attack...")
        # detect_callstack_attack()

        # if global_params.REPORT_MODE:
        #     rfile.write(str(total_no_of_paths) + "\n")

        # stop = time.time()
        if global_params.REPORT_MODE:
            rfile.write(str(dtime) + "\n")

        log.debug("Results for Reentrancy Bug: " + str(reentrancy_all_paths))
        # print("Results for Reentrancy Bug: " + str(reentrancy_all_paths))
        problem_result = check_list_empty(reentrancy_all_paths)
        # print("problem_result:", problem_result)

        if global_params.REPORT_MODE:
            if not problem_result:
                rfile.write("True" + "\n")
            else:
                rfile.write("False" + "\n")
            rfile.close()

        if not problem_result:
            detect_reentrancy()

            if global_params.CHECK_ASSERTIONS:
                if g_src_map:
                    detect_assertion_failure()
                else:
                    raise Exception("Assertion checks need a Source Map")

            if g_src_map:
                log_info()
        else:
            log.info("\t  Results for Reentrancy: \t\t False")

    else:
        log.info("\t  EVM code coverage: \t 0/0")
        log.info("\t  Reentrancy bug: \t False")
        if global_params.CHECK_ASSERTIONS:
            log.info("\t  Assertion failure: \t False")
        results["evm_code_coverage"] = "0/0"

    return results, vulnerability_found()

def log_info():
    global g_src_map
    global reentrancy
    global assertion_failure

    vulnerabilities = [reentrancy]
    if g_src_map:
        if global_params.CHECK_ASSERTIONS:
            vulnerabilities.append(assertion_failure)

    for vul in vulnerabilities:
        s = str(vul)
        if s:
            log.info(s)

def vulnerability_found():
    global g_src_map
    global reentrancy
    global assertion_failure

    if reentrancy is None:
        return 0
    vulnerabilities = [reentrancy]

    if g_src_map and global_params.CHECK_ASSERTIONS:
        vulnerabilities.append(assertion_failure)

    for vul in vulnerabilities:
        if vul.is_vulnerable():
            return 1
    return 0

def closing_message():
    global g_disasm_file
    global results

    log.info("\t====== Analysis Completed ======")
    if global_params.STORE_RESULT:
        result_file = g_disasm_file.split('.evm.disasm')[0] + '.json'
        with open(result_file, 'w') as of:
            of.write(json.dumps(results, indent=1))
        log.info("Wrote results to %s.", result_file)


def run_build_cfg_and_analyze(timeout_cb=do_nothing):
    initGlobalVars()
    global g_timeout

    try:
        with Timeout(sec=global_params.GLOBAL_TIMEOUT):
            build_cfg_and_analyze()
        log.debug('Done Symbolic execution')
    except TimeoutError:
        g_timeout = True
        timeout_cb()

def get_recipients(disasm_file, contract_address):
    global recipients
    global data_source
    global g_src_map
    global g_disasm_file
    global g_source_file

    g_src_map = None
    g_disasm_file = disasm_file
    g_source_file = None
    data_source = EthereumData(contract_address)
    recipients = set()

    evm_code_coverage = float(len(visited_pcs)) / len(instructions.keys())

    run_build_cfg_and_analyze()

    return {
        'addrs': list(recipients),
        'evm_code_coverage': evm_code_coverage,
        'timeout': g_timeout
    }

def test():
    global_params.GLOBAL_TIMEOUT = global_params.GLOBAL_TIMEOUT_TEST

    def timeout_cb():
        traceback.print_exc()
        exit(EXCEPTION)

    run_build_cfg_and_analyze(timeout_cb=timeout_cb)

def analyze():
    def timeout_cb():
        if global_params.DEBUG_MODE:
            traceback.print_exc()

    run_build_cfg_and_analyze(timeout_cb=timeout_cb)

def run(disasm_file=None, source_file=None, source_map=None):
    global g_disasm_file
    global g_source_file
    global g_src_map
    global results
    global begin

    g_disasm_file = disasm_file
    g_source_file = source_file  # source -> source_file
    g_src_map = source_map

    if is_testing_evm():
        test()
    else:
        begin = time.time()
        log.info("\t============ Results ===========")
        analyze()
        ret = detect_vulnerabilities()
        closing_message()  # store result file as json
        return ret
