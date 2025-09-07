module param_types_module #(
    parameter INT_P = 10,
    parameter real REAL_P = 3.14,
    parameter string STRING_P = "default",
    parameter type TYPE_P = logic
) (
    input logic in_a,
    input int in_b,
    output TYPE_P out_val
);
    localparam LOCAL_INT = INT_P * 2;
    localparam LOCAL_REAL = REAL_P + 1.0;
    typedef enum {RED, GREEN, BLUE} colors_t;
    parameter colors_t ENUM_P = GREEN;
    typedef struct packed {
        logic [7:0] data;
        logic enable;
    } my_struct_t;
    parameter my_struct_t STRUCT_P = '{data: 8'hAA, enable: 1'b1};
    parameter int ARRAY_P [3] = '{10, 20, 30};
    TYPE_P internal_val;
    wire [7:0] sub_inst_output_wire;
    always_comb begin
        internal_val = in_a ? TYPE_P'(LOCAL_INT + ARRAY_P[0]) : TYPE_P'(in_b);
        out_val = internal_val;
    end
    param_sub_module #(
        .SUB_INT_P(INT_P + LOCAL_INT),
        .SUB_REAL_P(REAL_P * 2.0),
        .SUB_STRING_P("override_str"),
        .SUB_TYPE_P(bit [7:0])
    ) sub_inst (
        .sub_in(in_a),
        .sub_out(sub_inst_output_wire)
    );
endmodule
module param_sub_module #(
    parameter int SUB_INT_P = 1,
    parameter real SUB_REAL_P = 1.0,
    parameter string SUB_STRING_P = "sub_default",
    parameter type SUB_TYPE_P = logic [3:0]
) (
    input logic sub_in,
    output SUB_TYPE_P sub_out
);
    SUB_TYPE_P internal_sub_val;
    always_comb begin
        internal_sub_val = SUB_TYPE_P'(SUB_INT_P + (sub_in ? 1 : 0));
        sub_out = internal_sub_val;
    end
endmodule
module gen_blocks_module #(
    parameter int MAX_INST = 2,
    parameter int LOOP_MAX_PARAM = 1,
    parameter int CASE_VAL_PARAM = 1
) (
    input logic sel_in,
    output int out_sum
);
    int sum_if_contrib = 0;
    int sum_case_contrib = 0;
    generate
        if (MAX_INST > 0) begin : gen_if_positive
            int const_if_val = MAX_INST * 10;
            always_comb begin
                sum_if_contrib = const_if_val;
            end
        end else begin : gen_if_negative
            int const_if_val = MAX_INST * 5;
            always_comb begin
                sum_if_contrib = const_if_val;
            end
        end
    endgenerate
    generate
        case (CASE_VAL_PARAM)
            1 : begin : case_1
                always_comb begin
                    sum_case_contrib = 100;
                end
            end
            2 : begin : case_2
                always_comb begin
                    sum_case_contrib = 200;
                end
            end
            default : begin : case_default
                always_comb begin
                    sum_case_contrib = 50;
                end
            end
        endcase
    endgenerate
    generate
        if (MAX_INST > 0) begin : gen_loop_and_sum
            int loop_inst_outputs[MAX_INST];
            for (genvar i = 0; i < MAX_INST; i++) begin : gen_loop_inst
                param_sub_module #(
                    .SUB_INT_P(LOOP_MAX_PARAM + i),
                    .SUB_TYPE_P(int)
                ) sub_loop_inst (
                    .sub_in(sel_in),
                    .sub_out(loop_inst_outputs[i])
                );
            end
            always_comb begin
                automatic int temp_sum = 0;
                for (int i = 0; i < MAX_INST; i++) begin
                    temp_sum = temp_sum + loop_inst_outputs[i];
                end
                out_sum = sum_if_contrib + sum_case_contrib + temp_sum;
            end
        end else begin : gen_no_loop_sum
            always_comb begin
                out_sum = sum_if_contrib + sum_case_contrib;
            end
        end
    endgenerate
endmodule
class MyParameterizedClass #(parameter int SIZE = 8);
    logic [SIZE-1:0] data;
    parameter int DEFAULT_VAL = 5;
    function new();
        data = SIZE'(DEFAULT_VAL);
    endfunction
    function logic [SIZE-1:0] get_data();
        return data;
    endfunction
    function int get_size();
        return SIZE;
    endfunction
    function automatic int get_modified_data(int multiplier);
        return data * multiplier;
    endfunction
endclass
module param_class_module (
    input int data_in,
    output int result_out
);
    int internal_result;
    MyParameterizedClass #(16) class_inst_16;
    MyParameterizedClass #(32) class_inst_32;
    always_comb begin
        if (class_inst_16 == null) begin
            class_inst_16 = new();
        end
        if (class_inst_32 == null) begin
            class_inst_32 = new();
        end
        internal_result = class_inst_16.get_data() + class_inst_32.get_modified_data(data_in);
        internal_result = internal_result + class_inst_16.DEFAULT_VAL;
        internal_result = internal_result + class_inst_32.get_size();
    end
    assign result_out = internal_result;
endmodule
interface param_iface #(parameter WIDTH = 8);
    logic [WIDTH-1:0] addr;
    logic [WIDTH-1:0] data;
    logic enable;
    function int get_width();
        return WIDTH;
    endfunction
    modport master (output addr, output data, output enable, import function int get_width());
    modport slave (input addr, input data, input enable);
endinterface
module param_iface_driver (
    input logic clk,
    input logic reset,
    output int current_width,
    param_iface.master master_if
);
    always_comb begin
        master_if.enable = reset ? 1'b0 : clk;
        master_if.addr = clk ? 'hFF : 'h00;
        master_if.data = clk ? 'h12 : 'h34;
        current_width = master_if.get_width();
    end
endmodule
module param_iface_top (
    input logic top_clk,
    input logic top_reset,
    output int interface_width_out
);
    param_iface #(16) my_interface_inst ();
    param_iface_driver driver_inst (
        .clk(top_clk),
        .reset(top_reset),
        .current_width(interface_width_out),
        .master_if(my_interface_inst)
    );
endmodule
(* hier_block *) module hier_block_param_module #(
    parameter int HB_WIDTH = 4,
    parameter string HB_MESSAGE = "hello"
) (
    input logic [HB_WIDTH-1:0] hb_in,
    output logic [HB_WIDTH-1:0] hb_out
);
    logic [HB_WIDTH-1:0] internal_reg;
    always_comb begin
        internal_reg = hb_in;
        hb_out = internal_reg + 1;
    end
endmodule
module hier_block_top (
    input logic [7:0] data_in,
    output logic [7:0] data_out,
    output logic [3:0] hb_out_2_val
);
    hier_block_param_module #(
        .HB_WIDTH(8),
        .HB_MESSAGE("custom_message")
    ) hb_inst_1 (
        .hb_in(data_in),
        .hb_out(data_out)
    );
    hier_block_param_module #(
        .HB_WIDTH(4),
        .HB_MESSAGE("hello")
    ) hb_inst_2 (
        .hb_in(data_in[3:0]),
        .hb_out(hb_out_2_val)
    );
endmodule
module recursive_module #(
    parameter int DEPTH = 0,
    parameter int MAX_DEPTH = 2
) (
    input int in_val,
    output int out_val
);
    int next_val;
    if (DEPTH < MAX_DEPTH) begin : recurse_inst
        recursive_module #(
            .DEPTH(DEPTH + 1),
            .MAX_DEPTH(MAX_DEPTH)
        ) next_level_inst (
            .in_val(in_val + 1),
            .out_val(next_val)
        );
    end else begin : base_case
        always_comb begin
            next_val = in_val;
        end
    end
    assign out_val = next_val;
endmodule
module recursive_top (
    input int start_val,
    output int final_val
);
    recursive_module #(
        .DEPTH(0),
        .MAX_DEPTH(3)
    ) top_recurse_inst (
        .in_val(start_val),
        .out_val(final_val)
    );
endmodule
module system_design (
    input logic main_clk,
    input logic main_reset,
    input int main_data_in,
    input logic main_sel_in,
    output int param_types_out_int,
    output bit [15:0] param_types_out_bit16,
    output int gen_blocks_sum_out,
    output int param_class_res_out,
    output int iface_width_out_1,
    output int iface_width_out_2,
    output logic [7:0] hier_block_out_1,
    output logic [3:0] hier_block_out_2,
    output int recursive_final_val
);
    param_types_module #(
        .INT_P(10),
        .REAL_P(3.14),
        .STRING_P("default"),
        .TYPE_P(logic)
    ) types_inst_default (
        .in_a(main_clk),
        .in_b(main_data_in),
        .out_val(param_types_out_int)
    );
    param_types_module #(
        .INT_P(25),
        .REAL_P(5.5),
        .STRING_P("another_string"),
        .TYPE_P(bit [15:0])
    ) types_inst_custom (
        .in_a(~main_clk),
        .in_b(main_data_in + 1),
        .out_val(param_types_out_bit16)
    );
    gen_blocks_module #(
        .MAX_INST(3),
        .LOOP_MAX_PARAM(10),
        .CASE_VAL_PARAM(2)
    ) gen_blocks_inst_1 (
        .sel_in(main_sel_in),
        .out_sum(gen_blocks_sum_out)
    );
    gen_blocks_module #(
        .MAX_INST(0),
        .LOOP_MAX_PARAM(1),
        .CASE_VAL_PARAM(1)
    ) gen_blocks_inst_2 (
        .sel_in(main_sel_in),
        .out_sum()
    );
    gen_blocks_module #(
        .MAX_INST(1),
        .LOOP_MAX_PARAM(5),
        .CASE_VAL_PARAM(3)
    ) gen_blocks_inst_3 (
        .sel_in(main_sel_in),
        .out_sum()
    );
    param_class_module class_mod_inst (
        .data_in(main_data_in),
        .result_out(param_class_res_out)
    );
    param_iface_top iface_top_inst_1 (
        .top_clk(main_clk),
        .top_reset(main_reset),
        .interface_width_out(iface_width_out_1)
    );
    param_iface #(8) my_interface_inst_2 ();
    param_iface_driver driver_inst_2 (
        .clk(main_clk),
        .reset(main_reset),
        .current_width(iface_width_out_2),
        .master_if(my_interface_inst_2)
    );
    hier_block_top hb_top_inst (
        .data_in(main_data_in[7:0]),
        .data_out(hier_block_out_1),
        .hb_out_2_val(hier_block_out_2)
    );
    recursive_top recurse_top_inst (
        .start_val(main_data_in),
        .final_val(recursive_final_val)
    );
endmodule
