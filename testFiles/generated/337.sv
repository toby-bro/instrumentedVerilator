module system_names_mod (
    input int in_val,
    output int out_val
);
    assign out_val = $bits(in_val);
endmodule

module snippet (
    input wire clk,
    input logic [2:0] inj_in_shift_1755007867369_295,
    input int inj_in_val_1755007867369_4,
    input logic [7:0] inj_in_val_1755007867369_647,
    input wire reset,
    output logic inj_o_sum_1755007867369_710,
    output logic [3:0] inj_out_part_1755007867369_987,
    output logic [7:0] inj_out_reg_1755007867369_337,
    output logic [7:0] inj_out_v_1755007867370_448,
    output int inj_out_val_1755007867369_777,
    output logic [7:0] inj_wide_reg_1755007867369_766
);
    // BEGIN: mod_lint_target_ts1755007867369
    logic l_reg_ts1755007867369;
        // BEGIN: module_assignments_in_loops_ts1755007867370
        localparam int PART_START = 4;
        localparam int PART_WIDTH = 4;
        logic [7:0] reg_var_ts1755007867370;
        logic [3:0] part_var_ts1755007867370;
            // BEGIN: ModVectorAdd_ts1755007867370
            assign inj_out_v_1755007867370_448 = reg_var_ts1755007867370 + 8'h01;
            // END: ModVectorAdd_ts1755007867370

        always_comb begin
            reg_var_ts1755007867370  = inj_in_val_1755007867369_647;
            part_var_ts1755007867370 = 4'h0;
            for (int i = 0; i < 4; i++) begin
                reg_var_ts1755007867370  = reg_var_ts1755007867370 + i;
                reg_var_ts1755007867370 += (i * 2);
                reg_var_ts1755007867370 <<= inj_in_shift_1755007867369_295;
                reg_var_ts1755007867370[i % 8] = (reg_var_ts1755007867370[i % 8] == 1'b0);
                reg_var_ts1755007867370[PART_START +: PART_WIDTH] = i[3:0];
            end
            part_var_ts1755007867370 = reg_var_ts1755007867370[7:4];
        end
        assign inj_out_reg_1755007867369_337  = reg_var_ts1755007867370;
        assign inj_out_part_1755007867369_987 = part_var_ts1755007867370;
        // END: module_assignments_in_loops_ts1755007867370

        system_names_mod system_names_mod_inst_1755007867369_7804 (
            .in_val(inj_in_val_1755007867369_4),
            .out_val(inj_out_val_1755007867369_777)
        );
    always_comb begin
        l_reg_ts1755007867369 = 1;
        inj_wide_reg_1755007867369_766 = {clk, reset};
    end
    assign inj_o_sum_1755007867369_710 = clk + reset;
    // END: mod_lint_target_ts1755007867369
endmodule

