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

module snippet (
    input wire clk,
    input wire [15:0] inj_i_packed_data_1755007808428_852,
    input logic [7:0] inj_op1_u_1755007808428_690,
    input logic [7:0] inj_op2_u_1755007808428_452,
    input wire reset,
    output logic [7:0] inj_diff_u_1755007808428_631,
    output logic [7:0] inj_o_member_sum_1755007808428_354,
    output logic [7:0] inj_prod_u_1755007808428_614,
    output logic [7:0] inj_sum_u_1755007808428_641
);
    // BEGIN: split_arith_blocking_ts1755007808428
    always @(*) begin
        inj_sum_u_1755007808428_641 = inj_op1_u_1755007808428_690 + inj_op2_u_1755007808428_452;
        inj_diff_u_1755007808428_631 = inj_op1_u_1755007808428_690 - inj_op2_u_1755007808428_452;
        inj_prod_u_1755007808428_614 = inj_op1_u_1755007808428_690 * inj_op2_u_1755007808428_452;
    end
    // END: split_arith_blocking_ts1755007808428

    module_struct module_struct_inst_1755007808428_785 (
        .i_packed_data(inj_i_packed_data_1755007808428_852),
        .o_member_sum(inj_o_member_sum_1755007808428_354)
    );
endmodule

