module snippet (
    input wire clk,
    input wire inj_g_ctrl_n_1755007836491_107,
    input wire [3:0] inj_in_a_1755007836491_969,
    input wire [3:0] inj_in_b_1755007836491_240,
    input wire [7:0] inj_in_c_1755007836491_369,
    input logic [7:0] inj_in_data_1755007836491_22,
    input wire reset,
    output wire inj_g_out_and_1755007836491_118,
    output wire inj_g_out_or_1755007836491_319,
    output logic inj_o_done_1755007836490_246,
    output logic [15:0] inj_out_concat_1755007836491_188,
    output logic [7:0] inj_out_if_else_1755007836491_662,
    output logic [7:0] inj_out_sum_1755007836491_94
);
    // BEGIN: mod_basic_ts1755007836490
    logic r_state_ts1755007836490;
        // BEGIN: simple_for_loop_ts1755007836491
        logic [7:0] sum_ts1755007836491;
            // BEGIN: module_concat_if_ts1755007836491
            always_comb begin
            inj_out_concat_1755007836491_188 = {inj_in_a_1755007836491_969, inj_in_b_1755007836491_240, inj_in_c_1755007836491_369};
            if (clk) begin
                inj_out_if_else_1755007836491_662 = inj_in_c_1755007836491_369;
            end else begin
                inj_out_if_else_1755007836491_662 = {inj_in_a_1755007836491_969, inj_in_b_1755007836491_240};
            end
            end
            // END: module_concat_if_ts1755007836491

            // BEGIN: Module_GatePrimitives_ts1755007836491
            and a1 (inj_g_out_and_1755007836491_118, reset, reset);
            or  o1 (inj_g_out_or_1755007836491_319 , reset, reset);
            // END: Module_GatePrimitives_ts1755007836491

        always_comb begin
            sum_ts1755007836491 = 8'h00;
            for (int i = 0; i < 5; i = i + 1) begin
                sum_ts1755007836491 = sum_ts1755007836491 + inj_in_data_1755007836491_22;
            end
            inj_out_sum_1755007836491_94 = sum_ts1755007836491;
        end
        // END: simple_for_loop_ts1755007836491

    parameter int PARAM_BASIC = 42;
    always_ff @(posedge clk) begin
        r_state_ts1755007836490 <= ~r_state_ts1755007836490;
    end
    always_comb begin
        inj_o_done_1755007836490_246 = r_state_ts1755007836490;
    end
    // END: mod_basic_ts1755007836490
endmodule

