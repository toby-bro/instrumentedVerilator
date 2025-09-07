module mod_err_event_constant (
    input wire clk,
    output logic dummy
);
    always @(posedge 1'b1) begin
        dummy = ~dummy;
    end
endmodule

module split_inputs_outputs_only (
    input logic [7:0] in_val_a_l,
    input logic [7:0] in_val_b_l,
    output logic [8:0] out_val_c_l,
    output logic [7:0] out_val_d_l
);
    always @(*) begin
        out_val_c_l = in_val_a_l + in_val_b_l;
        out_val_d_l = in_val_a_l - in_val_b_l;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755007883986_575,
    input int inj_b_1755007883986_320,
    input logic [1:0] inj_case_expr_1755007883987_913,
    input logic [7:0] inj_in_val_a_l_1755007883986_446,
    input logic [7:0] inj_in_val_b_l_1755007883986_353,
    input wire reset,
    output logic inj_dummy_1755007883986_310,
    output logic [4:0] inj_internal_out_1755007883987_556,
    output logic inj_out_a_1755007883986_330,
    output int inj_out_b_1755007883986_281,
    output logic [8:0] inj_out_val_c_l_1755007883986_416,
    output logic [7:0] inj_out_val_d_l_1755007883986_536
);
    // BEGIN: ModuleBasic_ts1755007883987
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c_ts1755007883987;
    int   d_ts1755007883987;
    always_comb begin
        logic temp_v_ts1755007883987;
            // BEGIN: case_full_parallel_mod_ts1755007883987
            always @* begin
                (* full, parallel *)
                case (inj_case_expr_1755007883987_913)
                    2'b00: inj_internal_out_1755007883987_556 = 1;
                    2'b01: inj_internal_out_1755007883987_556 = 2;
                    2'b10: inj_internal_out_1755007883987_556 = 3;
                    default: inj_internal_out_1755007883987_556 = 4;
                endcase
            end
            // END: case_full_parallel_mod_ts1755007883987

        temp_v_ts1755007883987 = d_ts1755007883987;
        c_ts1755007883987      = temp_v_ts1755007883987;
    end
    assign inj_out_a_1755007883986_330 = inj_a_1755007883986_575;
    assign d_ts1755007883987     = inj_b_1755007883986_320;
    assign inj_out_b_1755007883986_281 = d_ts1755007883987 + P1 + LP1;
    // END: ModuleBasic_ts1755007883987

    mod_err_event_constant mod_err_event_constant_inst_1755007883986_5042 (
        .clk(clk),
        .dummy(inj_dummy_1755007883986_310)
    );
    split_inputs_outputs_only split_inputs_outputs_only_inst_1755007883986_9900 (
        .out_val_d_l(inj_out_val_d_l_1755007883986_536),
        .in_val_a_l(inj_in_val_a_l_1755007883986_446),
        .in_val_b_l(inj_in_val_b_l_1755007883986_353),
        .out_val_c_l(inj_out_val_c_l_1755007883986_416)
    );
endmodule

