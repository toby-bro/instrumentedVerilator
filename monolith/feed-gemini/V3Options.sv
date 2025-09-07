`timescale 1ns/1ps
`define VERILATOR_MACRO_A 1
`define VERILATOR_MACRO_B "SystemVerilog"
module M_BasicFeatures (
    input logic [7:0] in_data_mf,
    input bit in_enable_mf,
    output logic [15:0] out_result_mf,
    output bit out_status_mf
);
    parameter int PARAM_INT_MF = 10;
    parameter string PARAM_STR_MF = "DefaultModuleString";
    localparam int LOCAL_PARAM_CALC_MF = PARAM_INT_MF * 2;
    logic [31:0] internal_reg_mf;
    bit [7:0][7:0] packed_array_mf;
    logic unpacked_array_mf [0:3];
    typedef struct packed {
        logic [3:0] field1;
        bit field2;
    } my_packed_struct_t;
    my_packed_struct_t my_struct_mf;
    always_comb begin
        internal_reg_mf = in_data_mf * LOCAL_PARAM_CALC_MF;
        if (in_enable_mf) begin
            internal_reg_mf = internal_reg_mf + PARAM_INT_MF;
            my_struct_mf.field1 = 4'hF;
            my_struct_mf.field2 = 1'b1;
        end else begin
            my_struct_mf.field1 = 4'h0;
            my_struct_mf.field2 = 1'b0;
        end
        out_result_mf = internal_reg_mf[15:0];
        out_status_mf = my_struct_mf.field2;
        for (int i = 0; i < 8; i++) begin
            packed_array_mf[i] = in_data_mf + i;
        end
        unpacked_array_mf[0] = in_enable_mf;
        unpacked_array_mf[1] = ~in_enable_mf;
        unpacked_array_mf[2] = 1'b0;
        unpacked_array_mf[3] = 1'b1;
    end
    `ifdef VERILATOR_MACRO_A
        logic defined_signal_mf;
        always_comb defined_signal_mf = `VERILATOR_MACRO_A ? in_enable_mf : 1'b0;
    `else
        logic defined_signal_else_mf;
        always_comb defined_signal_else_mf = 1'b1;
    `endif
endmodule
import "DPI-C" function int sv_multiply(input int a, input int b);
import "DPI-C" function string sv_get_constant_string();
module M_DPI_FileHandling (
    input int dpi_in_x,
    input int dpi_in_y,
    output int dpi_out_product,
    output string dpi_out_message
);
    logic [31:0] internal_product;
    string message_val;
    class DPIContext;
        int last_product;
        function new();
            last_product = 0;
        endfunction
        function void update_product(int p);
            last_product = p;
        endfunction
    endclass
    DPIContext dpi_ctx;
    always_comb begin
        internal_product = sv_multiply(dpi_in_x, dpi_in_y);
        dpi_out_product = internal_product;
        message_val = sv_get_constant_string();
        dpi_out_message = message_val;
        if (dpi_ctx == null) begin
            dpi_ctx = new();
        end
        dpi_ctx.update_product(dpi_out_product);
    end
endmodule
module M_CoverageAssertions (
    input logic [2:0] state_input_ca,
    input logic trigger_ca,
    input logic valid_data_ca,
    input logic [7:0] data_value_ca,
    output logic assertion_pass_ca
);
    logic [1:0] current_fsm_state_ca;
    always_ff @(posedge trigger_ca) begin
        case (state_input_ca)
            3'b000: current_fsm_state_ca <= 2'b00;
            3'b001: current_fsm_state_ca <= 2'b01;
            3'b010: current_fsm_state_ca <= 2'b10;
            default: current_fsm_state_ca <= 2'b11;
        endcase
    end
    covergroup StateAndDataCoverage @(posedge trigger_ca);
        state_cp: coverpoint state_input_ca {
            bins s_idle = {3'b000};
            bins s_active = {3'b001};
            bins s_done = {3'b010};
            bins s_error = {3'b011};
            option.weight = 1;
        }
        data_cp: coverpoint data_value_ca {
            bins range_low = {0, 1, 2, 3};
            bins range_mid = {[10:20]};
            bins range_high = {[250:255]};
            bins single_val = {128};
            option.goal = 90;
        }
        state_data_cross_cp: cross state_cp, data_cp {
            ignore_bins invalid_cross = binsof(state_cp) intersect {3'b111};
        }
    endgroup
    StateAndDataCoverage sc_inst = new();
    property check_data_on_active_state;
        @(posedge trigger_ca) (current_fsm_state_ca == 2'b01) |=> valid_data_ca;
    endproperty
    assert property (check_data_on_active_state) assertion_pass_ca = 1'b1; else assertion_pass_ca = 1'b0;
    property check_always_valid_value;
        @(data_value_ca) (data_value_ca >= 0);
    endproperty
    assert property (check_always_valid_value);
endmodule
module M_AdvancedTypesAndLoops (
    input byte in_byte_atl,
    input bit [3:0] selector_atl,
    output int out_sum_atl,
    output shortint out_mode_atl
);
    typedef enum {
        MODE_IDLE,
        MODE_PROCESS,
        MODE_FINISH
    } processing_mode_e;
    processing_mode_e current_mode_atl;
    typedef union packed {
        logic [31:0] full_word;
        logic [3:0][7:0] bytes;
        struct packed {
            logic [15:0] low_half;
            logic [15:0] high_half;
        } halves;
    } my_complex_union_t;
    my_complex_union_t union_inst_atl;
    logic [7:0] data_matrix [3][3];
    logic [7:0] processed_matrix [3][3];
    logic [127:0] ultra_wide_data;
    logic [63:0] complex_expr;
    logic enable_flow;
    always_comb begin
        out_sum_atl = 0;
        current_mode_atl = MODE_IDLE;
        for (int r = 0; r < 3; r++) begin
            for (int c = 0; c < 3; c++) begin
                data_matrix[r][c] = in_byte_atl + r + c;
                processed_matrix[r][c] = data_matrix[r][c] * 2;
                out_sum_atl += processed_matrix[r][c];
            end
        end
        case (selector_atl)
            4'h0: current_mode_atl = MODE_IDLE;
            4'h1: current_mode_atl = MODE_PROCESS;
            4'h2: current_mode_atl = MODE_FINISH;
            default: current_mode_atl = MODE_IDLE;
        endcase
        out_mode_atl = current_mode_atl;
        union_inst_atl.full_word = {processed_matrix[0][0], processed_matrix[0][1], processed_matrix[0][2], processed_matrix[1][0]};
        ultra_wide_data = {union_inst_atl.full_word, union_inst_atl.full_word, union_inst_atl.full_word, union_inst_atl.full_word};
        ultra_wide_data = ultra_wide_data + (out_sum_atl * 2);
        if (current_mode_atl == MODE_PROCESS) begin
            out_sum_atl += union_inst_atl.halves.low_half;
        end
        complex_expr = (out_sum_atl >> 2) + (in_byte_atl & selector_atl);
        enable_flow = (selector_atl == 4'h0);
        if (enable_flow) begin
            out_sum_atl = out_sum_atl + complex_expr;
        end
    end
endmodule
module M_ClockingAndHierarchy (
    input wire clk_ch,
    input wire rst_n_ch,
    input logic [3:0] control_in_ch,
    output logic [7:0] data_out_ch
);
    logic [7:0] internal_data_ch;
    logic secondary_clk_sig;
    clocking master_cb @(posedge clk_ch);
        output internal_data_ch;
        input control_in_ch;
        default input #1ns output #2ns;
    endclocking
    class DataLogger;
        int log_entries[$];
        function new();
            log_entries = {};
        endfunction
        function void log(int val);
            log_entries.push_back(val);
        endfunction
    endclass
    DataLogger logger_inst;
    always_ff @(master_cb) begin
        if (!rst_n_ch) begin
            internal_data_ch <= 8'h00;
        end else begin
            internal_data_ch <= master_cb.control_in_ch + 1;
        end
    end
    assign data_out_ch = internal_data_ch;
    always_comb begin
        if (logger_inst == null) begin
            logger_inst = new();
        end
        logger_inst.log(internal_data_ch);
    end
    M_BasicFeatures #(.PARAM_INT_MF(200), .PARAM_STR_MF("HierarchicalOverride"))
    u_basic_features_inst (
        .in_data_mf(control_in_ch),
        .in_enable_mf(secondary_clk_sig),
        .out_result_mf(),
        .out_status_mf(secondary_clk_sig)
    );
endmodule
module M_OptimizationTargets (
    input logic [63:0] op_A_ot,
    input logic [63:0] op_B_ot,
    input logic [2:0] op_mode_ot,
    output logic [63:0] final_result_ot
);
    logic [63:0] temp_val_ot_1, temp_val_ot_2, intermediate_ot_calc;
    logic [127:0] wide_intermediate_ot;
    logic [63:0] complex_expr;
    logic enable_flow;
    always_comb begin
        temp_val_ot_1 = op_A_ot;
        temp_val_ot_2 = op_B_ot;
        case (op_mode_ot)
            3'b000: begin
                intermediate_ot_calc = (temp_val_ot_1 + temp_val_ot_2) << 2;
                final_result_ot = intermediate_ot_calc;
            end
            3'b001: begin
                intermediate_ot_calc = (temp_val_ot_1 - temp_val_ot_2) >> 1;
                wide_intermediate_ot = {temp_val_ot_2, temp_val_ot_1} - {temp_val_ot_1, temp_val_ot_2};
                final_result_ot = intermediate_ot_calc & wide_intermediate_ot[63:0];
            end
            3'b010: begin
                if (op_A_ot > op_B_ot) begin
                    if (op_mode_ot[0]) begin
                        final_result_ot = op_A_ot;
                    end else begin
                        final_result_ot = op_A_ot + 1;
                    end
                end else if (op_A_ot < op_B_ot) begin
                    final_result_ot = op_B_ot;
                end else begin
                    final_result_ot = op_A_ot | op_B_ot;
                end
            end
            3'b011: begin
                intermediate_ot_calc = ~op_A_ot + 1;
                intermediate_ot_calc = intermediate_ot_calc * 3;
                if (intermediate_ot_calc == 0) begin
                    temp_val_ot_1 = 64'hFEED_FACE;
                end
                final_result_ot = intermediate_ot_calc;
            end
            default: begin
                logic [7:0] byte_segments[8];
                logic [63:0] reassembled_val;
                reassembled_val = op_A_ot ^ op_B_ot;
                for (int i=0; i<8; i++) begin
                    byte_segments[i] = reassembled_val[i*8 +: 8];
                end
                final_result_ot = {byte_segments[0], byte_segments[1], byte_segments[2], byte_segments[3],
                                   byte_segments[4], byte_segments[5], byte_segments[6], byte_segments[7]};
            end
        endcase
        complex_expr = (final_result_ot >> 4) + (op_A_ot & op_B_ot);
        enable_flow = (op_mode_ot == 3'b000);
        if (enable_flow) begin
            final_result_ot = complex_expr;
        end
    end
endmodule
module M_EnvInfo (
    input bit query_enable_ei,
    output string verilator_root_path_ei,
    output string systemc_include_path_ei
);
    `define VL_ROOT_PATH_DEFAULT "/usr/local/share/verilator"
    `define SC_INC_PATH_DEFAULT "/opt/systemc/include"
    class EnvironmentData;
        string root_val;
        string sc_inc_val;
        function new(string root, string sc_inc);
            root_val = root;
            sc_inc_val = sc_inc;
        endfunction
        function string get_root();
            return root_val;
        endfunction
        function string get_sc_inc();
            return sc_inc_val;
        endfunction
    endclass
    EnvironmentData env_data_inst;
    string internal_root_path;
    string internal_sc_inc_path;
    always_comb begin
        if (query_enable_ei) begin
            verilator_root_path_ei = `VL_ROOT_PATH_DEFAULT;
            systemc_include_path_ei = `SC_INC_PATH_DEFAULT;
        end else begin
            verilator_root_path_ei = "";
            systemc_include_path_ei = "";
        end
        if (env_data_inst == null) begin
            env_data_inst = new(`VL_ROOT_PATH_DEFAULT, `SC_INC_PATH_DEFAULT);
        end
        internal_root_path = env_data_inst.get_root();
        internal_sc_inc_path = env_data_inst.get_sc_inc();
    end
endmodule
module M_MiscOptionsTrigger (
    input int debug_level_in,
    input bit json_output_enable,
    output int current_debug_setting,
    output int process_result
);
    typedef struct {
        int id;
        logic [7:0] value;
        string name;
    } complex_info_t;
    class OptionTracker;
        int option_id;
        function new(int id);
            this.option_id = id;
        endfunction
        function int get_option_id();
            return option_id;
        endfunction
    endclass
    logic [15:0] data_val_mot;
    logic [15:0] processed_val_mot;
    complex_info_t info_item;
    OptionTracker tracker_inst;
    always_comb begin
        data_val_mot = debug_level_in + 10;
        processed_val_mot = data_val_mot * 2;
        current_debug_setting = debug_level_in;
        process_result = processed_val_mot;
        info_item.id = process_result;
        info_item.value = data_val_mot[7:0];
        info_item.name = json_output_enable ? "Enabled" : "Disabled";
        if (tracker_inst == null) begin
            tracker_inst = new(info_item.id);
        end
        process_result = tracker_inst.get_option_id();
    end
endmodule
