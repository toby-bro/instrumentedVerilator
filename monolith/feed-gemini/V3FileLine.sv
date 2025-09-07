module LineDirectiveTests (
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    `line 100 "test_files/generated_file_1.sv" 1
    logic [7:0] internal_reg_0;
    `line 200 "test_files/macro_expansion_src.svh" 0
    always_comb begin : comb_block_A
        `line 300 "test_files/logic_block.v" 1
        if (in_data > 127) begin
            internal_reg_0 = in_data + 1;
        end else begin
            internal_reg_0 = in_data - 1;
        end
        `line 305 "test_files/logic_block.v" 2
    end
    `line 205 "test_files/macro_expansion_src.svh" 2
    `line 400 "test_files/bad_level.sv" 0
    assign out_data = internal_reg_0;
    `line 105 "test_files/generated_file_1.sv" 2
    `line 500 "another_generated_file.sv" 1
    logic dummy_sig_a = 1'b0;
    `line 501 "another_generated_file.sv" 2
    `line 600 "yet_another_include.svh" 0
    logic dummy_sig_b = 1'b1;
    `line 601 "yet_another_include.svh" 2
endmodule
module PragmaWarningTests (
    input  bit clk,
    input  bit reset,
    input  int input_val,
    output int output_val,
    output int additional_output_val
);
    parameter int UNUSED_PARAM = 10;
    logic [3:0] unused_signal_a;
    logic [3:0] unused_signal_b;
    (* verilator_off_UNUSED *)
    always_comb begin
        unused_signal_a = input_val[3:0];
    end
    (* verilator_on_UNUSED *)
    logic [7:0] impl_lint_signal;
    logic [31:0] output_val_implicit_style;
    (* verilator_off_LINT *)
    assign impl_lint_signal = input_val[7:0] + 1;
    assign output_val_implicit_style = input_val + 2;
    (* verilator_on_LINT *)
    logic [1:0] selector;
    assign selector = input_val[1:0];
    (* verilator_off_STYLE *)
    always_comb begin
        case (selector)
            2'b00: output_val = 1;
            2'b01: output_val = 2;
            2'b00: output_val = 3;
            default: output_val = 0;
        endcase
    end
    (* verilator_on_STYLE *)
    assign additional_output_val = input_val + (unused_signal_a[0] ? 1 : 0) + (impl_lint_signal[0] ? 1 : 0);
endmodule
module ComplexLogicAndTypes (
    input  bit                     clk,
    input  bit                     rst_n,
    input  logic [15:0]            input_bus,
    input  byte                    byte_in,
    input  enum {STATE_IDLE, STATE_ACTIVE, STATE_DONE} current_state_in,
    output logic [31:0]            result_data_out,
    output int                     sum_val,
    output bit                     status_flag
);
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
    } MyPackedStruct;
    typedef union packed {
        logic [15:0] full_word;
        MyPackedStruct parts;
    } MyPackedUnion;
    typedef logic [3:0] DynamicArray_t [];
    typedef int AssociativeArray_t [string];
    MyPackedStruct      reg_struct_var;
    MyPackedUnion       reg_union_var;
    DynamicArray_t      dyn_array;
    AssociativeArray_t  assoc_array;
    logic [15:0] local_reg_a, local_reg_b;
    logic [7:0]  loop_idx;
    logic [63:0] wide_reg;
    string       message_str;
    int          queue_var [$];
    byte         fixed_array [4];
    class MySimpleClass;
        rand int class_data_a;
        int class_data_b;
        function new(int init_val);
            class_data_a = init_val;
            class_data_b = init_val * 2;
        endfunction
        function int get_sum();
            return class_data_a + class_data_b;
        endfunction
    endclass : MySimpleClass
    MySimpleClass class_obj_inst;
    logic [31:0] result_data_comb;
    logic [31:0] result_data_latch;
    logic [31:0] result_data_gen [2];
    always_ff @(posedge clk or negedge rst_n) begin : ff_block
        if (!rst_n) begin
            local_reg_a <= 16'h0;
            local_reg_b <= 16'h0;
            reg_struct_var.field_a <= 8'h0;
            reg_struct_var.field_b <= 8'h0;
            reg_union_var.full_word <= 16'h0;
            if (class_obj_inst == null) begin
                class_obj_inst = new(input_bus);
            end
        end else begin
            local_reg_a <= input_bus;
            local_reg_b <= input_bus + 1;
            reg_struct_var.field_a <= byte_in;
            reg_struct_var.field_b <= byte_in + 1;
            reg_union_var.parts.field_a <= byte_in;
            if (class_obj_inst != null) begin
                class_obj_inst.class_data_a = input_bus + 5;
            end
        end
    end
    always_comb begin : comb_block_B
        result_data_comb = 32'h0;
        sum_val = 0;
        status_flag = 1'b0;
        message_str = "Default message";
        if (local_reg_a > local_reg_b) begin
            result_data_comb = {local_reg_a, local_reg_b};
            message_str = "A is greater than B";
        end else if (local_reg_a == local_reg_b) begin
            result_data_comb = 32'hDEADBEEF;
            message_str = "A equals B";
        end else begin
            result_data_comb = {local_reg_b, local_reg_a};
            message_str = "B is greater than A";
        end
        case (current_state_in)
            STATE_IDLE: begin
                sum_val = byte_in;
                status_flag = 1'b0;
            end
            STATE_ACTIVE: begin
                sum_val = byte_in * 2;
                status_flag = 1'b1;
            end
            STATE_DONE: begin
                sum_val = byte_in + 100;
                status_flag = 1'b1;
            end
            default: begin
                sum_val = -1;
                status_flag = 1'b0;
            end
        endcase
        for (loop_idx = 0; loop_idx < 8; loop_idx++) begin
            sum_val += loop_idx;
        end
        if (byte_in > 5) begin
            dyn_array = new[byte_in % 10 + 1];
            foreach (dyn_array[k]) begin
                dyn_array[k] = k;
            end
            sum_val += dyn_array.size();
        end else begin
            dyn_array = new[0];
        end
        assoc_array["first_key"] = 10;
        assoc_array["second_key"] = 20;
        if (assoc_array.exists("first_key")) begin
            sum_val += assoc_array["first_key"];
        end
        queue_var.push_back(byte_in);
        if (queue_var.size() > 0) begin
            sum_val += queue_var.pop_front();
        end
        for (int j=0; j<4; j++) begin
            fixed_array[j] = byte_in + j;
            sum_val += fixed_array[j];
        end
        if (class_obj_inst != null) begin
            sum_val += class_obj_inst.get_sum();
        end
        wide_reg = {input_bus, local_reg_a, byte_in, reg_struct_var.field_a, reg_union_var.full_word, loop_idx, 16'hAAAA};
        result_data_comb = wide_reg[31:0];
    end
    always_latch begin : latch_block
        if (status_flag) begin
            result_data_latch = input_bus;
        end else begin
            result_data_latch = 32'h0;
        end
    end
    genvar i;
    generate
        if (1) begin : gen_if_block
            for (i=0; i<2; i++) begin : gen_for_block
                localparam int GENERATED_PARAM = i * 10;
                logic [7:0] generated_local_var;
                always_comb begin
                    generated_local_var = input_bus[7:0] + GENERATED_PARAM;
                end
                assign result_data_gen[i] = {24'h0, generated_local_var};
            end
        end
    endgenerate
    assign result_data_out = result_data_comb + result_data_latch + result_data_gen[0] + result_data_gen[1];
endmodule
module ChildModule (
    input  logic [7:0] child_in,
    output logic [7:0] child_out
);
    logic [7:0] declared_local_var;
    logic [3:0] narrow_signal;
    assign declared_local_var = child_in + 5;
    assign child_out = declared_local_var;
    assign narrow_signal = child_in;
endmodule
module ParentModule (
    input  logic [15:0] parent_in,
    output logic [15:0] parent_out
);
    logic [7:0] internal_child_in;
    logic [7:0] internal_child_out;
    logic [7:0] unused_signal_in_parent;
    logic [7:0] macro_context_var = 8'hC0;
    ChildModule child_inst_1 (
        .child_in  (parent_in[7:0]),
        .child_out (internal_child_out)
    );
    `define MACRO_SIMPLE_OP(VAL) (VAL + macro_context_var)
    logic [7:0] macro_result_a;
    assign macro_result_a = `MACRO_SIMPLE_OP(parent_in[7:0]);
    genvar g;
    generate for (g=0; g<1; g++) begin : gen_block
        localparam UNUSED_GEN_PARAM = g + 1;
    end endgenerate
    assign parent_out = {8'h0, internal_child_out} + {8'h0, macro_result_a};
endmodule
