module param_basic_module #(
    parameter int P_WIDTH = 8,
    parameter logic [P_WIDTH-1:0] P_DEFAULT_VAL = 8'hAA
) (
    input logic [P_WIDTH-1:0] in_data,
    output logic [P_WIDTH-1:0] out_data
);
    localparam int L_DOUBLE_WIDTH = P_WIDTH * 2;
    localparam logic [P_WIDTH-1:0] L_COMPLEMENT_VAL = ~P_DEFAULT_VAL;
    assign out_data = in_data ^ L_COMPLEMENT_VAL;
endmodule
module param_type_module #(
    parameter type P_DATA_T = logic [7:0]
) (
    input P_DATA_T in_val,
    output P_DATA_T out_val
);
    assign out_val = ~in_val;
endmodule
module param_string_module #(
    parameter string P_MSG = "Hello_Verilog",
    parameter int P_MSG_LEN = P_MSG.len()
) (
    input logic [7:0] in_char_idx,
    output logic [7:0] out_char_code
);
    assign out_char_code = (in_char_idx < P_MSG_LEN) ? P_MSG[in_char_idx] : 8'h00;
endmodule
module param_real_module #(
    parameter real P_THRESHOLD = 0.5,
    parameter real P_GAIN = 2.0
) (
    input real in_real_val,
    output real out_real_val
);
    assign out_real_val = (in_real_val > P_THRESHOLD) ? (in_real_val * P_GAIN) : (in_real_val / P_GAIN);
endmodule
module param_gen_if_module #(
    parameter int P_MODE = 0,
    parameter int P_DATA_WIDTH = 4
) (
    input logic [P_DATA_WIDTH-1:0] in_a,
    input logic [P_DATA_WIDTH-1:0] in_b,
    output logic [P_DATA_WIDTH-1:0] out_result
);
    generate
        if (P_MODE == 0) begin : gen_and
            assign out_result = in_a & in_b;
        end else if (P_MODE == 1) begin : gen_or
            assign out_result = in_a | in_b;
        end else begin : gen_xor
            assign out_result = in_a ^ in_b;
        end
    endgenerate
endmodule
module param_gen_for_module #(
    parameter int P_NUM_STAGES = 3,
    parameter int P_STAGE_WIDTH = 4
) (
    input logic [P_STAGE_WIDTH-1:0] in_val,
    output logic [P_STAGE_WIDTH-1:0] out_val
);
    logic [P_STAGE_WIDTH-1:0] stage_regs [P_NUM_STAGES];
    generate
        genvar i;
        for (i = 0; i < P_NUM_STAGES; i = i + 1) begin : gen_stage
            if (i == 0) begin
                assign stage_regs[i] = in_val;
            end else begin
                assign stage_regs[i] = stage_regs[i-1];
            end
        end
    endgenerate
    assign out_val = stage_regs[P_NUM_STAGES-1];
endmodule
module param_gen_case_module #(
    parameter int P_FUNCTION_SEL = 0,
    parameter int P_OPERAND_WIDTH = 8
) (
    input logic [P_OPERAND_WIDTH-1:0] op_a,
    input logic [P_OPERAND_WIDTH-1:0] op_b,
    output logic [P_OPERAND_WIDTH*2-1:0] op_result
);
    generate
        case (P_FUNCTION_SEL)
            0: begin : gen_add
                assign op_result = op_a + op_b;
            end
            1: begin : gen_sub
                assign op_result = op_a - op_b;
            end
            default: begin : gen_mul
                assign op_result = op_a * op_b;
            end
        endcase
    endgenerate
endmodule
interface param_iface #(
    parameter int IF_WIDTH = 4
) (
    input logic clk,
    input logic rst
);
    logic [IF_WIDTH-1:0] data;
    logic valid;
    logic ready;
    modport master (output data, output valid, input ready, input clk, input rst);
    modport slave (input data, input valid, output ready, input clk, input rst);
endinterface
module param_interface_module (
    input logic clk,
    input logic rst,
    input int in_if_width,
    output logic out_valid
);
    param_iface #(in_if_width) iface_inst (.clk(clk), .rst(rst));
    always_comb begin
        iface_inst.data = 0;
        iface_inst.valid = 0;
        iface_inst.ready = 1;
        if (clk && !rst) begin
            iface_inst.data = 1;
            iface_inst.valid = 1;
        end
    end
    assign out_valid = iface_inst.valid;
endmodule
class param_my_class #(
    parameter int C_ID = 10,
    parameter string C_NAME = "default"
);
    int value;
    function new(int init_val);
        value = init_val + C_ID;
    endfunction
    function int get_value();
        return value;
    endfunction
    function string get_name();
        return C_NAME;
    endfunction
endclass
module param_class_module (
    input logic clk,
    input int in_id_offset,
    input string in_name_suffix,
    output int out_class_value,
    output string out_class_name
);
    param_my_class #(100 + in_id_offset, {"MyClass_", in_name_suffix}) class_inst;
    always_comb begin
        class_inst = new(5);
        out_class_value = class_inst.get_value();
        out_class_name = class_inst.get_name();
    end
endmodule
module param_hier_ref_module #(
    parameter int TOP_VAL = 5
) (
    input logic [7:0] in_val,
    output logic [7:0] out_sum
);
    logic [7:0] data_basic_0;
    logic [7:0] data_basic_1;
    logic [7:0] data_basic_2;
    param_basic_module #(.P_WIDTH(8), .P_DEFAULT_VAL(8'h11)) inst_basic_0 (
        .in_data(in_val),
        .out_data(data_basic_0)
    );
    param_basic_module #(.P_WIDTH(TOP_VAL), .P_DEFAULT_VAL(8'h22)) inst_basic_1 (
        .in_data(in_val),
        .out_data(data_basic_1)
    );
    param_basic_module #(.P_WIDTH(4), .P_DEFAULT_VAL(8'h33)) inst_basic_2 (
        .in_data(in_val[3:0]),
        .out_data(data_basic_2[3:0])
    );
    assign out_sum = data_basic_0 + data_basic_1 + data_basic_2;
    param_my_class #(.C_ID(TOP_VAL + 20), .C_NAME("ComplexInstance")) complex_class_inst;
    int complex_val;
    string complex_name;
    always_comb begin
        complex_class_inst = new(10);
        complex_val = complex_class_inst.get_value();
        complex_name = complex_class_inst.get_name();
    end
endmodule
module param_array_module #(
    parameter int P_ARRAY_SIZE = 3,
    parameter int P_ARRAY [P_ARRAY_SIZE] = '{10, 20, 30}
) (
    input int in_idx,
    output int out_val_at_idx
);
    assign out_val_at_idx = (in_idx >= 0 && in_idx < P_ARRAY_SIZE) ? P_ARRAY[in_idx] : 0;
endmodule
module param_complex_default_module #(
    parameter int BASE_OFFSET = 5,
    parameter int FINAL_VALUE = BASE_OFFSET * 2 + 1
) (
    input int in_trigger,
    output int out_computed_value
);
    assign out_computed_value = in_trigger + FINAL_VALUE;
endmodule
