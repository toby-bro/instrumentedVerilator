module split_complex_blocking (
    input logic [7:0] i1_r,
    input logic [7:0] i2_r,
    input logic [7:0] i3_r,
    output logic [7:0] o1_r,
    output logic [7:0] o2_r,
    output logic [7:0] o3_r
);
    logic [7:0] t1_r, t2_r;
    always @(*) begin
        t1_r = i1_r + i2_r;
        o1_r = t1_r - i3_r;
        t2_r = i2_r * i3_r;
        o2_r = t1_r + t2_r;
        o3_r = t2_r / 2;
    end
endmodule

module split_multiple_in_branch (
    input logic clk_j,
    input logic condition_j,
    input logic [7:0] in_a_j,
    input logic [7:0] in_b_j,
    output logic [7:0] out_x_j,
    output logic [7:0] out_y_j
);
    always @(posedge clk_j) begin
        if (condition_j) begin
            out_x_j <= in_a_j * 3;
            out_y_j <= in_b_j + 1;
        end else begin
            out_x_j <= in_a_j;
            out_y_j <= in_b_j;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_i1_r_1755007863138_196,
    input logic [7:0] inj_i2_r_1755007863138_433,
    input logic [7:0] inj_i3_r_1755007863138_343,
    input logic [15:0] inj_in_1755007863138_416,
    input logic inj_in_a_1755007863139_441,
    input wire reset,
    output logic [7:0] inj_o1_r_1755007863138_849,
    output logic [7:0] inj_o2_r_1755007863138_223,
    output logic [7:0] inj_o3_r_1755007863138_102,
    output logic [15:0] inj_out_1755007863138_229,
    output logic inj_out_a_1755007863139_397,
    output logic [7:0] inj_out_sum_1755007863139_390,
    output logic [7:0] inj_out_x_j_1755007863139_461,
    output logic [7:0] inj_out_y_j_1755007863139_348
);
    // BEGIN: always_comb_assign_ts1755007863139
    // BEGIN: mod_name_conflict_ts1755007863139
    logic conflict_var_ts1755007863139;
        // BEGIN: simple_for_loop_ts1755007863140
        logic [7:0] sum_ts1755007863140;
        always_comb begin
            sum_ts1755007863140 = 8'h00;
            for (int i = 0; i < 5; i = i + 1) begin
                sum_ts1755007863140 = sum_ts1755007863140 + inj_i1_r_1755007863138_196;
            end
            inj_out_sum_1755007863139_390 = sum_ts1755007863140;
        end
        // END: simple_for_loop_ts1755007863140

        split_multiple_in_branch split_multiple_in_branch_inst_1755007863139_7580 (
            .condition_j(inj_in_a_1755007863139_441),
            .in_a_j(inj_i1_r_1755007863138_196),
            .in_b_j(inj_i2_r_1755007863138_433),
            .out_x_j(inj_out_x_j_1755007863139_461),
            .out_y_j(inj_out_y_j_1755007863139_348),
            .clk_j(clk)
        );
    parameter int conflict_param = 1;
    assign inj_out_a_1755007863139_397 = inj_in_a_1755007863139_441;
    // END: mod_name_conflict_ts1755007863139

    always_comb begin
        inj_out_1755007863138_229 = inj_in_1755007863138_416;
    end
    // END: always_comb_assign_ts1755007863139

    split_complex_blocking split_complex_blocking_inst_1755007863138_3958 (
        .i1_r(inj_i1_r_1755007863138_196),
        .i2_r(inj_i2_r_1755007863138_433),
        .i3_r(inj_i3_r_1755007863138_343),
        .o1_r(inj_o1_r_1755007863138_849),
        .o2_r(inj_o2_r_1755007863138_223),
        .o3_r(inj_o3_r_1755007863138_102)
    );
endmodule

