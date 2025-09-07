module mod_casez_wildcard (
    input bit [3:0] in_mask_z,
    output bit [1:0] out_match_type_z
);
always_comb begin
    casez (in_mask_z)
        4'b10?0: begin
            out_match_type_z = 2'b00;
        end
        4'b011?: begin
            out_match_type_z = 2'b01;
        end
        default: begin
            out_match_type_z = 2'b11;
        end
    endcase
end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_add_val_m1_1755007785329_355,
    input logic inj_cond_in_1755007785328_670,
    input wire [7:0] inj_d_in_1755007785329_164,
    input logic [3:0] inj_in_h_1755007785329_652,
    input logic [3:0] inj_in_l_1755007785329_514,
    input bit [3:0] inj_in_mask_z_1755007785329_701,
    input logic [7:0] inj_in_val_m1_1755007785329_211,
    input wire reset,
    output logic inj_cond_out_1755007785328_740,
    output logic [7:0] inj_out_c_1755007785329_894,
    output bit [1:0] inj_out_match_type_z_1755007785329_871,
    output logic [7:0] inj_out_sum_m1_1755007785329_9,
    output reg [7:0] inj_q_out_1755007785329_414,
    output logic [7:0] inj_var_out_m1_1755007785329_888
);
    // BEGIN: mod_logical_not_ts1755007785329
    // BEGIN: concat_op_ts1755007785329
    // BEGIN: expr_preadd_comb_ts1755007785329
    logic [7:0] var_m1_ts1755007785329;
        // BEGIN: Seq_DFF_ts1755007785330
        always_ff @(posedge clk or posedge reset) begin
            if (reset) begin
                inj_q_out_1755007785329_414 <= 8'b0;
            end else begin
                inj_q_out_1755007785329_414 <= inj_d_in_1755007785329_164;
            end
        end
        // END: Seq_DFF_ts1755007785330

    always_comb begin
        var_m1_ts1755007785329 = inj_in_val_m1_1755007785329_211;
        inj_out_sum_m1_1755007785329_9 = (++var_m1_ts1755007785329) + inj_add_val_m1_1755007785329_355;
        inj_var_out_m1_1755007785329_888 = var_m1_ts1755007785329;
    end
    // END: expr_preadd_comb_ts1755007785329

    mod_casez_wildcard mod_casez_wildcard_inst_1755007785329_3652 (
        .out_match_type_z(inj_out_match_type_z_1755007785329_871),
        .in_mask_z(inj_in_mask_z_1755007785329_701)
    );
    assign inj_out_c_1755007785329_894 = {inj_in_h_1755007785329_652, inj_in_l_1755007785329_514};
    // END: concat_op_ts1755007785329

    always_comb begin
        inj_cond_out_1755007785328_740 = !inj_cond_in_1755007785328_670;
    end
    // END: mod_logical_not_ts1755007785329
endmodule

