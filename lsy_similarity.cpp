#include "dr_api.h"
#include "drmgr.h"
#include "drwrap.h"
#include "drsyms.h"
#include "drx.h"
#include "droption.h"
#include <string>
#include <tuple>
#include <vector>
#include <fstream>
#include <iostream>
#include <algorithm>
#include <cctype>
#include <set>
#include <utility>
#include <thread>
#include <chrono>

// static void *count_mutex; /* for multithread support */

std::vector<std::vector<std::tuple<uint, std::string, int>>> runtime_vals;
std::vector<std::tuple<uint, std::string, int>> once_runtime_vals;

static int prev_dst_nums = 0;
static int prev_idx = -1;
static bool need = false;
opnd_t prev_op1, prev_op2;
char prev_buf[256];

struct InstrTParts {
    std::string opcode;
    std::vector<std::string> srcs;
    std::vector<std::string> dsts;
};

struct InstructionParts {
    std::string opcode;
    std::vector<std::string> eles;
};

std::vector<std::string> source_insts_;
std::vector<InstructionParts> source_insts;

//---------------------匹配处理------------------

InstrTParts split_instr_t(const char buf[256]) {
    InstrTParts parts;
    std::string instruction(buf); // 转换为 std::string

    size_t arrowPos = instruction.find("->");
    DR_ASSERT(arrowPos != std::string::npos);

    std::string leftPart = instruction.substr(0, arrowPos);
    std::istringstream leftStream(leftPart);
    leftStream >> parts.opcode;

    // 分割源操作数
    std::string src;
    while (leftStream >> src) {
        parts.srcs.push_back(src);
    }

    std::string rightPart = instruction.substr(arrowPos + 2); // 获取 "->" 右边的部分
    rightPart.erase(0, rightPart.find_first_not_of(" \t")); // 去除前导空格
    std::istringstream rightStream(rightPart);
    std::string dst;
    while (rightStream >> dst) {
        parts.dsts.push_back(dst);
    }

    return parts;
}

InstructionParts split_instruction(std::string instruction) {
    InstructionParts parts;

    std::istringstream stream(instruction);
    stream >> parts.opcode;

    std::string element;
    while (getline(stream, element, ',')) {
        // 去除前后空格
        element.erase(remove_if(element.begin(), element.end(), ::isspace), element.end());
        if (!element.empty()) {
            parts.eles.push_back(element);
        }
    }

    return parts;
}

void read_instructions_from_file(const std::string &filename) {
    std::ifstream file(filename);

    if (!file.is_open()) {
        std::cerr << "Error opening file: " << filename << std::endl;
    }

    std::string line;
    while (std::getline(file, line)) {
        // 去除行首尾的空格
        line.erase(0, line.find_first_not_of(" \t"));
        line.erase(line.find_last_not_of(" \t") + 1);

        if (!line.empty() && line.back() != ':' && line != "ret") {
            source_insts_.push_back(line);
        }
    }

    file.close();

    for(const auto& inst : source_insts_)
        source_insts.push_back(split_instruction(inst));
}

std::vector<std::string> extract_elements_from_mem(const std::string& str) {
    std::vector<std::string> elements;
    
    std::string cleaned = str.substr(1, str.length() - 2); // 去掉开头的 '[' 和结尾的 ']'
    
    // 使用逗号分割
    std::istringstream stream(cleaned);
    std::string element;
    
    while (getline(stream, element, ',')) {
        // 去除前后空格
        element.erase(remove_if(element.begin(), element.end(), ::isspace), element.end());
        elements.push_back(element); // 添加到元素列表
    }
    
    return elements;
}

bool compareEQ(InstructionParts inst1, InstrTParts inst2) {
    if ((inst1.opcode != inst2.opcode) &&
    !( (inst1.opcode == "mov" && inst2.opcode == "movz") || 
       (inst1.opcode == "mov" && inst2.opcode == "orr") )) {
        return false;
    }

    auto isReg = [](std::string s) -> bool {
        if(s[0] == 'w' || s[0] == 'x' || s[0] == 'q' || s[0] == 'v' || s[0] == 'd')
            return true;
        return false;
    };

    auto isNumber = [](const std::string& str) -> bool {
        if (str.empty()) return false;
        if (str[0] == '-') {
            return str.length() > 1 && std::all_of(str.begin() + 1, str.end(), ::isdigit);
        }

        return std::all_of(str.begin(), str.end(), ::isdigit);
    };

    int i = 0;
    for(int j = 0; i < inst1.eles.size() && j < inst2.dsts.size(); i++, j++){
        auto ele = inst1.eles[i];
        auto dst = inst2.dsts[j];
        if(isReg(ele)) {
            if(dst[0] != '%')   return false;
            if(ele != dst.substr(1))    return false;
        } else if(ele[0] == '[') {
            for(const auto& e : extract_elements_from_mem(ele)) {
                size_t pos = dst.find(e);
                if (pos != std::string::npos) {
                // 如果找到，剔除子串
                    dst.erase(pos, e.length());
                } else {
                    return false;
                }
            }
        }    
    }

    for(int j = 0; i < inst1.eles.size() && j < inst2.srcs.size(); i++, j++){
        auto ele = inst1.eles[i];
        auto src = inst2.srcs[j];
        if(isReg(ele)) {
            if(src[0] != '%')   return false;
            if(ele != src.substr(1))    return false;
        } else if(isNumber(ele)) {
            if(src[0] != '$')   return false;
            std::istringstream iss1(ele);
            uint64_t num1 = 0;
            num1 = ele[0] == '-' ? std::stoll(ele) : std::stoull(ele);
            std::istringstream iss2(src.substr(1));
            uint64_t num2 = 0;
            iss2 >> std::hex >> num2;
            if(num1 != num2)    return false;
        } else if(ele[0] == '[') {
            for(const auto& e : extract_elements_from_mem(ele)) {
                size_t pos = src.find(e);
                if (pos != std::string::npos) {
                // 如果找到，剔除子串
                    src.erase(pos, e.length());
                } else {
                    return false;
                }
            }
        } 
    }
    return true;
}

//------------------------找共同特征处理------------
std::vector<std::tuple<uint, std::string, int>> find_common_elements() {
    // dr_fprintf(STDERR, "Begin to find.\n");
    if (runtime_vals.empty()) return {};

    // 使用 set 存储第一个 vector 的元素
    std::set<std::tuple<uint, std::string, int>> common_elements(runtime_vals[0].begin(), runtime_vals[0].end());

    for (size_t i = 1; i < runtime_vals.size(); ++i) {
        std::set<std::tuple<uint, std::string, int>> current_set(runtime_vals[i].begin(), runtime_vals[i].end());
        
        // 计算交集
        std::set<std::tuple<uint, std::string, int>> temp;
        std::set_intersection(common_elements.begin(), common_elements.end(),
                              current_set.begin(), current_set.end(),
                              std::inserter(temp, temp.begin()));
        
        // 更新 common_elements
        common_elements.swap(temp);
    }
    return std::vector<std::tuple<uint, std::string, int>>(common_elements.begin(), common_elements.end());
}

//------------------------dynamorio----------------

static void
callback1(int idx, uint op1)
{
    // dr_mutex_lock(count_mutex);

    // dr_fprintf(STDERR, "val1: %d\n", op1);
    once_runtime_vals.push_back({op1, "", idx});

    // dr_mutex_unlock(count_mutex);
}

static void
callback2(int idx, uint op1, uint op2)
{
    // dr_mutex_lock(count_mutex);

    // dr_fprintf(STDERR, "val1: %d\n", op1);
    // dr_fprintf(STDERR, "val2: %d\n", op2);
    once_runtime_vals.push_back({op1, "", idx});
    once_runtime_vals.push_back({op2, "", idx});

    // dr_mutex_unlock(count_mutex);
}

static bool
instr_is_need(instr_t *instr, DR_PARAM_OUT opnd_t *opnd1, DR_PARAM_OUT opnd_t *opnd2, DR_PARAM_OUT int *idx, const char* buf)
{
    if(!instr_valid(instr))
        return false;

    int opc = instr_get_opcode(instr);
    int num_dst = instr_num_dsts(instr);

    #if defined(X86)
    if (opc == OP_div) {
        *opnd = instr_get_src(instr, 0); /* divisor is 1st src */
        return true;
    }
#elif defined(AARCHXX)
    if (opc == OP_subs || opc == OP_msr || opc == OP_mrs) {
        return false;
    }
#elif defined(RISCV64)
    if (opc == OP_divu) {
        *opnd = instr_get_src(instr, 1); /* divisor is 2nd src */
        return true;
    }
#else
#    error NYI
#endif

    if(num_dst == 0)
        return false;
    
    // DR_ASSERT(num_dst <= 2);

    // 确认是不是我们源程序中的指令之一
    bool is_source = false;
    InstrTParts inst_buf = split_instr_t(buf);
    for(int i = 0; i < source_insts.size(); i++) {
        auto inst_source = source_insts[i];
        if(compareEQ(inst_source, inst_buf)) {
            is_source = true;
            *idx = i;
            break;
        }
    }
    if(!is_source)
        return false;

    // fixme 我们需要的应该没有有2个操作数以上的
    *opnd1 = instr_get_dst(instr, 0);
    if(num_dst > 1)
        *opnd2 = instr_get_dst(instr, 1);

    return true;
}

static std::pair<bool, opnd_t> adjust_opnd(opnd_t& op) {

    if(!(opnd_is_reg_pointer_sized(op) || opnd_is_reg(op)))
        return {false, op};
    // if(opnd_is_base_disp(op))

    if (opnd_is_reg(op)) {
        reg_id_t reg = opnd_get_reg(op);
        if(reg_is_simd(reg))
            return {false, op};
        op = opnd_create_reg(reg_to_pointer_sized(reg));
    }

    return {true, op};
}

                      /* This is called separately for each instruction in the block. */
static dr_emit_flags_t
event_app_instruction(void *drcontext, void *tag, instrlist_t *bb, instr_t *instr,
                      bool for_trace, bool translating, void *user_data)
{
    drmgr_disable_auto_predication(drcontext, bb);

    // if(drmgr_is_first_instr(drcontext, instr)) {
    //     byte buffer[128]; 
    //     byte *encoded_pc = instr_encode(drcontext, instr, buffer);
    //     dr_fprintf(STDERR, "iii: %s\n", buffer);
    // }

    int num_srcs = instr_num_srcs(instr);
    int num_dsts = instr_num_dsts(instr);

    char buf[256];
    instr_disassemble_to_buffer(drcontext, instr, buf, sizeof(buf));
        
    // dr_fprintf(STDERR, "Instruction1: %s, num dst : %d, num src : %d\n", buf, num_dsts, num_srcs);

    if(drmgr_is_first_instr(drcontext, instr)) {
        need = false;
        prev_idx = -1;
    }

    // 处理上一条
    if(need) {
        // dr_fprintf(STDERR, "go go for : \n");
        // dr_fprintf(STDERR, "Instruction2: %s\n", prev_buf);
        if(prev_dst_nums == 2) {
            dr_insert_clean_call(drcontext, bb, instr, (void *)callback2, false /*no fp save*/,
                            3, OPND_CREATE_INTPTR(prev_idx), prev_op1, prev_op2);
            
        } else {
            DR_ASSERT(prev_dst_nums == 1);
            dr_insert_clean_call(drcontext, bb, instr, (void *)callback1, false /*no fp save*/,
                            2, OPND_CREATE_INTPTR(prev_idx), prev_op1);
        }
    }

    memcpy(prev_buf, buf, sizeof(buf));

    opnd_t opnd1, opnd2;
    int idx = -1;
    bool cur_need = instr_is_need(instr, &opnd1, &opnd2, &idx, buf);
    if(cur_need) {
        bool valid1, valid2;

        std::tie(valid1, prev_op1) = adjust_opnd(opnd1);
        if(valid1) {
            if(num_dsts > 1) {
                std::tie(valid2, prev_op2) = adjust_opnd(opnd2);
                if(valid2) {
                    DR_ASSERT(opnd_is_reg_pointer_sized(prev_op1));
                    DR_ASSERT(opnd_is_reg_pointer_sized(prev_op2));
                    prev_dst_nums = 2;
                    prev_idx = idx;
                } else 
                    cur_need = false;
            } else {
                prev_dst_nums = 1;
                prev_idx = idx;
            }
        } else 
            cur_need = false;
    }

    need = cur_need;
    
    return DR_EMIT_DEFAULT;
}

namespace dynamorio {
namespace samples_ {
namespace {

using ::dynamorio::droption::DROPTION_SCOPE_CLIENT;
using ::dynamorio::droption::droption_t;

static droption_t<std::string> trace_function(
    DROPTION_SCOPE_CLIENT, "trace_function", "_Z7wrap_fnPFmvE", "Name of function to trace",
    "The name of the function to wrap and print callstacks on every call.");

static void
wrap_pre(void *wrapcxt, DR_PARAM_OUT void **user_data)
{
    // dr_fprintf(STDERR, "%s called from:\n", trace_function.get_value().c_str());
    if (!drmgr_register_bb_instrumentation_event(NULL, event_app_instruction, NULL))
        DR_ASSERT(false);
}

static void
wrap_post(void *wrapcxt, DR_PARAM_OUT void *user_data)
{
    if (!drmgr_unregister_bb_insertion_event(event_app_instruction))
        DR_ASSERT(false);
    for(int i = 0; i < once_runtime_vals.size(); i++) {
        std::get<1>(once_runtime_vals[i]) = source_insts_[std::get<2>(once_runtime_vals[i])];
    }
    // for(const auto& val : once_runtime_vals) {
    //     std::cout << std::get<0>(val) << " " << std::get<1>(val) << " " << std::get<2>(val) << std::endl;
    // }
    runtime_vals.push_back(once_runtime_vals);
    once_runtime_vals.clear();
    // dr_fprintf(STDERR, "runtime vals size : %d.\n", runtime_vals.size());
    // dr_fprintf(STDERR, "%s finished.\n", trace_function.get_value().c_str());
}

static void
module_load_event(void *drcontext, const module_data_t *mod, bool loaded)
{
    size_t modoffs;
    drsym_error_t sym_res = drsym_lookup_symbol(
        mod->full_path, trace_function.get_value().c_str(), &modoffs, DRSYM_DEMANGLE);
    if (sym_res == DRSYM_SUCCESS) {
        app_pc towrap = mod->start + modoffs;
        bool ok = drwrap_wrap(towrap, wrap_pre, wrap_post);
        DR_ASSERT(ok);
        dr_fprintf(STDERR, "wrapping %s!%s\n", mod->full_path,
                   trace_function.get_value().c_str());
    }
}

static void
module_unload_event(void *drcontext, const module_data_t *mod)
{
    size_t modoffs;
    drsym_error_t sym_res = drsym_lookup_symbol(
        mod->full_path, trace_function.get_value().c_str(), &modoffs, DRSYM_DEMANGLE);
    // dr_fprintf(STDERR, "unload modoffs : %s\n", modoffs);
    if (sym_res == DRSYM_SUCCESS) {
        app_pc towrap = mod->start + modoffs;
        bool ok = drwrap_unwrap(towrap, wrap_pre, NULL);
        DR_ASSERT(ok);
    }
}

static void
event_exit()
{
    // 第二种, 记录所有runtime values改cost func
    std::ofstream outfile_val("all_vals.txt");
    if (!outfile_val) {
        dr_fprintf(STDERR, "Error opening file: all_vals.txt\n");
        return;
    }

    for(const auto& once_vals : runtime_vals) {
        for(const auto& val : once_vals) {
            outfile_val << std::get<0>(val) << " ";
        }
        outfile_val << "\n";
    }
    outfile_val.close();
    

    //------------------------------

    dr_fprintf(STDERR, "runtime vals size : %d.\n", runtime_vals.size());
    std::vector<std::tuple<uint, std::string, int>> common = find_common_elements();
    // dr_fprintf(STDERR, "common size : %d.\n", common.size());
    // for(int i = 0; i < common.size(); i++) {
    //     dr_fprintf(STDERR, "common : %s.\n", std::get<1>(common[i]).c_str());
    // }

    std::ofstream outfile("common.txt");
    if (!outfile) {
        dr_fprintf(STDERR, "Error opening file: common.txt\n");
        return;
    }

    for (const auto& elem : common) {
        // outfile << std::get<0>(elem) << " <- " << std::get<1>(elem) << ".  from : " << std::get<2>(elem) << std::endl;
        outfile << std::get<2>(elem) << "\n";
    }
    outfile.close();
    runtime_vals.clear();
    // dr_fprintf(STDERR, "Exiting DynamoRIO client...\n");
    drmgr_register_module_unload_event(module_unload_event);
    drwrap_exit();
    drmgr_exit();
    drx_exit();
    drsym_exit();
}

} // namespace
} // namespace samples
} // namespace dynamorio

DR_EXPORT void
dr_client_main(client_id_t id, int argc, const char *argv[])
{
    dr_set_client_name("DynamoRIO Sample Client 'callstack'",
                       "http://dynamorio.org/issues");
    read_instructions_from_file("/usr/local/software/source.s");
    // Parse our option.
    if (!dynamorio::droption::droption_parser_t::parse_argv(
            dynamorio::droption::DROPTION_SCOPE_CLIENT, argc, argv, NULL, NULL))
        DR_ASSERT(false);

    // Initialize the libraries we're using.
    if (!drwrap_init() || !drmgr_init() || !drx_init() ||
        drsym_init(0) != DRSYM_SUCCESS ||
        !drmgr_register_module_load_event(dynamorio::samples_::module_load_event))
        DR_ASSERT(false);
    dr_register_exit_event(dynamorio::samples_::event_exit);
    // Improve performance as we only need basic wrapping support.
    drwrap_set_global_flags(
        static_cast<drwrap_global_flags_t>(DRWRAP_NO_FRILLS | DRWRAP_FAST_CLEANCALLS));
}