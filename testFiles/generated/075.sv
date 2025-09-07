module concat_op (
    input logic [3:0] in_h,
    input logic [3:0] in_l,
    output logic [7:0] out_c
);
    assign out_c = {in_h, in_l};
endmodule

module module_function (
    input wire [7:0] in_func_a,
    input wire [7:0] in_func_b,
    output logic [7:0] out_func_result
);
    function automatic [7:0] add_and_subtract;
    input [7:0] val1;
    input [7:0] val2;
    reg [7:0] temp;
    begin
    temp = val1 + val2;
    add_and_subtract = temp - 1;
    end
    endfunction
    always_comb begin
    out_func_result = add_and_subtract(in_func_a, in_func_b);
    end
endmodule

module module_struct (
    input wire [15:0] i_packed_data,
    output logic [7:0] o_member_sum
);
    typedef struct packed {
        logic [3:0] part1;
        logic [7:0] part2;
        logic [3:0] part3;
    } my_packed_struct_t;
    my_packed_struct_t unpacked_data;
    assign unpacked_data = i_packed_data;
    always @* begin
        o_member_sum = unpacked_data.part1 + unpacked_data.part2 + unpacked_data.part3;
    end
endmodule

module split_if_only_then (
    input logic clk_h,
    input logic condition_h,
    input logic [7:0] in_val_h,
    output logic [7:0] out_reg_h
);
    always @(posedge clk_h) begin
        if (condition_h) begin
            out_reg_h <= in_val_h;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_condition_h_1755007777109_429,
    input wire [15:0] inj_i_packed_data_1755007777110_962,
    input wire [7:0] inj_in_func_a_1755007777108_48,
    input wire [7:0] inj_in_func_b_1755007777108_413,
    input logic [3:0] inj_in_h_1755007777108_459,
    input logic [3:0] inj_in_l_1755007777108_825,
    input logic [7:0] inj_in_val_h_1755007777109_421,
    input wire reset,
    output logic [7:0] inj_o_member_sum_1755007777110_702,
    output logic [7:0] inj_out_c_1755007777108_497,
    output logic [7:0] inj_out_func_result_1755007777108_124,
    output logic [7:0] inj_out_reg_h_1755007777109_348
);
    module_struct module_struct_inst_1755007777110_1677 (
        .o_member_sum(inj_o_member_sum_1755007777110_702),
        .i_packed_data(inj_i_packed_data_1755007777110_962)
    );
    split_if_only_then split_if_only_then_inst_1755007777109_1701 (
        .out_reg_h(inj_out_reg_h_1755007777109_348),
        .clk_h(clk),
        .condition_h(inj_condition_h_1755007777109_429),
        .in_val_h(inj_in_val_h_1755007777109_421)
    );
    module_function module_function_inst_1755007777108_5053 (
        .in_func_a(inj_in_func_a_1755007777108_48),
        .in_func_b(inj_in_func_b_1755007777108_413),
        .out_func_result(inj_out_func_result_1755007777108_124)
    );
    concat_op concat_op_inst_1755007777108_7585 (
        .in_h(inj_in_h_1755007777108_459),
        .in_l(inj_in_l_1755007777108_825),
        .out_c(inj_out_c_1755007777108_497)
    );
endmodule

