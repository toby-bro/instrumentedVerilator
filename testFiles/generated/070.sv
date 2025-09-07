interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module ConcatVectorOps (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [7:0] c,
    output logic [15:0] out_concat
);
    assign out_concat = {a, b, c};
endmodule

module concat_assign (
    input logic [7:0] in,
    output logic [3:0] out_h,
    output logic [3:0] out_l
);
    assign {out_h, out_l} = in;
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007775330_314,
    input wire [2:0] inj_count_in_1755007775328_814,
    input logic inj_d_in_1755007775328_448,
    input logic [7:0] inj_in_data_1755007775328_789,
    input int inj_in_val_1755007775328_989,
    input logic [3:0] inj_v1_1755007775328_34,
    input logic [3:0] inj_v2_1755007775328_305,
    input wire reset,
    output logic inj_and_reduce_1755007775331_917,
    output wire [2:0] inj_count_out_1755007775328_546,
    output logic inj_eq_1755007775328_524,
    output logic [4:0] inj_internal_out_1755007775330_282,
    output logic inj_or_reduce_1755007775331_978,
    output logic [1:0] inj_out_bits_1755007775328_251,
    output logic [15:0] inj_out_concat_1755007775329_113,
    output logic [3:0] inj_out_h_1755007775331_327,
    output logic [3:0] inj_out_l_1755007775331_577,
    output int inj_out_val_1755007775328_380,
    output logic inj_out_valid_status_1755007775329_740,
    output logic inj_q_out_1755007775328_244,
    output logic inj_xor_reduce_1755007775331_145
);
    // BEGIN: cast_select_demo_ts1755007775328
    logic [7:0] internal_ts1755007775328;
        // BEGIN: LogicDependencyChain_ts1755007775328
        logic q1_ts1755007775328, q2_ts1755007775328;
            // BEGIN: simple_seq_ts1755007775328
            reg [2:0] counter_reg_ts1755007775328;
                concat_assign concat_assign_inst_1755007775331_41 (
                    .in(inj_in_data_1755007775328_789),
                    .out_h(inj_out_h_1755007775331_327),
                    .out_l(inj_out_l_1755007775331_577)
                );
                // BEGIN: ReductionOperations_ts1755007775331
                assign inj_and_reduce_1755007775331_917 = &internal_ts1755007775328;
                assign inj_or_reduce_1755007775331_978 = |internal_ts1755007775328;
                assign inj_xor_reduce_1755007775331_145 = ^internal_ts1755007775328;
                // END: ReductionOperations_ts1755007775331

                // BEGIN: case_unique0_violating_mod_ts1755007775330
                always @* begin
                    unique0 casez (inj_case_expr_1755007775330_314)
                        2'b1?: inj_internal_out_1755007775330_282 = 8;
                        2'b11: inj_internal_out_1755007775330_282 = 9;  
                        2'b?1: inj_internal_out_1755007775330_282 = 10; 
                        2'b00: inj_internal_out_1755007775330_282 = 11; 
                    endcase
                end
                // END: case_unique0_violating_mod_ts1755007775330

                // BEGIN: module_assign_blocking_ts1755007775329
                my_if vif_inst();
                always_comb begin
                    vif_inst.data = inj_in_data_1755007775328_789;
                    vif_inst.valid = 1'b1;
                    vif_inst.ready = 1'b0;
                    inj_out_valid_status_1755007775329_740 = vif_inst.valid;
                end
                // END: module_assign_blocking_ts1755007775329

                ConcatVectorOps ConcatVectorOps_inst_1755007775329_6317 (
                    .c(internal_ts1755007775328),
                    .out_concat(inj_out_concat_1755007775329_113),
                    .a(inj_v1_1755007775328_34),
                    .b(inj_v2_1755007775328_305)
                );
            always @(posedge clk or posedge reset) begin
                if (reset) begin
                    counter_reg_ts1755007775328 <= 3'b000;
                end else begin
                    counter_reg_ts1755007775328 <= inj_count_in_1755007775328_814 + 3'b001;
                end
            end
            assign inj_count_out_1755007775328_546 = counter_reg_ts1755007775328;
            // END: simple_seq_ts1755007775328

            // BEGIN: local_not_allowed_diag_mod_ts1755007775328
            assign inj_out_val_1755007775328_380 = inj_in_val_1755007775328_989;
            // END: local_not_allowed_diag_mod_ts1755007775328

        always @(posedge clk) begin
            q1_ts1755007775328 <= inj_d_in_1755007775328_448;
        end
        always @(q1_ts1755007775328) begin
            q2_ts1755007775328 = ~q1_ts1755007775328;
        end
        assign inj_q_out_1755007775328_244 = q2_ts1755007775328;
        // END: LogicDependencyChain_ts1755007775328

        // BEGIN: ModCompareVec_ts1755007775328
        assign inj_eq_1755007775328_524 = (inj_v1_1755007775328_34 == inj_v2_1755007775328_305);
        // END: ModCompareVec_ts1755007775328

    always_comb begin
        internal_ts1755007775328 = inj_in_data_1755007775328_789;
        inj_out_bits_1755007775328_251 = internal_ts1755007775328[3 -: 2];
    end
    // END: cast_select_demo_ts1755007775328
endmodule

