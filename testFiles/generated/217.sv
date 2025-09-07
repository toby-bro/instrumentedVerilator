interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module ConditionalOps (
    input logic sel,
    input int val_false,
    input int val_true,
    output int out_val
);
    assign out_val = sel ? val_true : val_false;
endmodule

module ModuleFF (
    input logic clk,
    input bit [3:0] in1,
    input bit [3:0] in2,
    input logic reset,
    output bit [3:0] out1,
    output bit [3:0] out2
);
    parameter int MAX_COUNT = 10;
    localparam int START_VAL = 5;
    logic [3:0] ff_reg;
    integer unused_int_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            ff_reg <= START_VAL;
            out1 <= '0;
            out2 <= '0;
            unused_int_var <= 0;
        end else begin
            case ({in1, in2})
                8'h00: ff_reg <= ff_reg;
                8'h01: ff_reg <= in1 + in2;
                default: ff_reg <= MAX_COUNT;
            endcase
            out1 <= ff_reg;
            out2 <= {in1[0], in1[0], in1[0], in1[0]} | {in2[3], in2[2], in2[1], in2[0]};
        end
    end
endmodule

module ReductionOperations (
    input logic [7:0] data_in,
    output logic and_reduce,
    output logic or_reduce,
    output logic xor_reduce
);
    assign and_reduce = &data_in;
    assign or_reduce = |data_in;
    assign xor_reduce = ^data_in;
endmodule

module loop_with_internal_assign (
    input logic [3:0] start_val,
    output logic [7:0] final_val
);
    logic [7:0] current_val;
    always_comb begin
        current_val = start_val;
        for (int k = 0; k < 3; k = k + 1) begin
            current_val = current_val + 1;
        end
        final_val = current_val;
    end
endmodule

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module module_assign_blocking (
    input logic [7:0] in_data,
    output logic out_valid_status
);
    my_if vif_inst();
    always_comb begin
        vif_inst.data = in_data;
        vif_inst.valid = 1'b1;
        vif_inst.ready = 1'b0;
        out_valid_status = vif_inst.valid;
    end
endmodule

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module snippet #(
    parameter integer UNUSED_PARAM = 8
) (
    input wire clk,
    input logic [3:0] inj_data0_1755007826327_119,
    input logic [3:0] inj_data1_1755007826327_503,
    input logic [3:0] inj_data2_1755007826327_422,
    input logic [7:0] inj_i_target_data_1755007826303_598,
    input bit [3:0] inj_in1_1755007826307_882,
    input logic [15:0] inj_in1_1755007826321_412,
    input bit [3:0] inj_in2_1755007826307_654,
    input logic [15:0] inj_in_1755007826311_513,
    input logic [2:0] inj_in_val_1755007826330_265,
    input logic [1:0] inj_sel_1755007826303_109,
    input logic inj_sel_1755007826303_707,
    input logic [3:0] inj_start_val_1755007826305_403,
    input logic inj_uin_1755007826309_641,
    input int inj_val_false_1755007826303_540,
    input int inj_val_true_1755007826303_119,
    input wire reset,
    output logic inj_and_reduce_1755007826305_530,
    output logic [3:0] inj_data_out_case_1755007826327_232,
    output wire inj_dout_1755007826313_54,
    output logic [7:0] inj_final_val_1755007826305_716,
    output wire inj_loop_out_1755007826319_758,
    output logic inj_nm_out_1755007826306_937,
    output logic [7:0] inj_o_result_1755007826315_981,
    output logic inj_o_status_1755007826315_733,
    output logic [7:0] inj_o_target_result_1755007826303_948,
    output logic inj_or_reduce_1755007826305_976,
    output bit [3:0] inj_out1_1755007826307_848,
    output logic [15:0] inj_out1_1755007826321_203,
    output bit [3:0] inj_out2_1755007826307_625,
    output logic [15:0] inj_out2_1755007826321_871,
    output logic [15:0] inj_out_1755007826311_484,
    output logic inj_out_c_1755007826316_419,
    output logic [7:0] inj_out_case_a_1755007826303_402,
    output logic [7:0] inj_out_case_b_1755007826303_549,
    output logic inj_out_n_1755007826308_261,
    output logic [3:0] inj_out_part_1755007826332_274,
    output logic [7:0] inj_out_reg_1755007826332_109,
    output reg inj_out_res_1755007826330_68,
    output logic inj_out_sub_1755007826324_270,
    output int inj_out_val_1755007826303_130,
    output logic [7:0] inj_out_val_1755007826303_161,
    output logic inj_out_valid_status_1755007826312_610,
    output logic inj_udnt_output_1755007826309_362,
    output logic inj_uout_1755007826309_471,
    output logic inj_xor_reduce_1755007826305_18
);
    // BEGIN: target_module_for_bind_ts1755007826303
    // BEGIN: used_before_declared_diag_mod_ts1755007826303
    logic [7:0] undeclared_var_ubddm = 8'd5;
    // BEGIN: mod_split_case_ts1755007826304
    logic [7:0]  split_case_var_ts1755007826304;
    logic [7:0] other_case_var_ts1755007826304;
        // BEGIN: ContinuousWire_ts1755007826313
        wire internal_w_ts1755007826313;
            // BEGIN: basic_assign_if_ts1755007826317
            logic intermediate_wire_ts1755007826317;
                // BEGIN: Comb_Loop_ts1755007826319
                wire loop_wire1_ts1755007826319;
                wire loop_wire2_ts1755007826319;
                    // BEGIN: procedural_complex_ts1755007826321
                    logic [15:0] temp1_ts1755007826321;
                    logic [15:0] temp2_ts1755007826321;
                        // BEGIN: module_assignments_in_loops_ts1755007826333
                        localparam int PART_START = 4;
                        localparam int PART_WIDTH = 4;
                        logic [7:0] reg_var_ts1755007826333;
                        logic [3:0] part_var_ts1755007826333;
                        always_comb begin
                            reg_var_ts1755007826333  = split_case_var_ts1755007826304;
                            part_var_ts1755007826333 = 4'h0;
                            for (int i = 0; i < 4; i++) begin
                                reg_var_ts1755007826333  = reg_var_ts1755007826333 + i;
                                reg_var_ts1755007826333 += (i * 2);
                                reg_var_ts1755007826333 <<= inj_in_val_1755007826330_265;
                                reg_var_ts1755007826333[i % 8] = (reg_var_ts1755007826333[i % 8] == 1'b0);
                                reg_var_ts1755007826333[PART_START +: PART_WIDTH] = i[3:0];
                            end
                            part_var_ts1755007826333 = reg_var_ts1755007826333[7:4];
                        end
                        assign inj_out_reg_1755007826332_109  = reg_var_ts1755007826333;
                        assign inj_out_part_1755007826332_274 = part_var_ts1755007826333;
                        // END: module_assignments_in_loops_ts1755007826333

                        // BEGIN: casez_xz_alt_ts1755007826330
                        always_comb begin
                            inj_out_res_1755007826330_68 = 1'b0;
                            casez (inj_in_val_1755007826330_265)
                                3'b1?z: inj_out_res_1755007826330_68 = 1'b1;
                                3'b0z?: inj_out_res_1755007826330_68 = 1'b0;
                                default: inj_out_res_1755007826330_68 = 1'b1;
                            endcase
                        end
                        // END: casez_xz_alt_ts1755007826330

                        // BEGIN: case_selector_ts1755007826327
                        always_comb begin
                            case (inj_sel_1755007826303_109)
                                2'b00: inj_data_out_case_1755007826327_232 = inj_data0_1755007826327_119; 
                                2'b01: inj_data_out_case_1755007826327_232 = inj_data1_1755007826327_503; 
                                2'b10: inj_data_out_case_1755007826327_232 = inj_data2_1755007826327_422; 
                                default: inj_data_out_case_1755007826327_232 = inj_start_val_1755007826305_403; 
                            endcase
                        end
                        // END: case_selector_ts1755007826327

                        // BEGIN: mod_sub_ts1755007826324
                        assign inj_out_sub_1755007826324_270 = internal_w_ts1755007826313;
                        // END: mod_sub_ts1755007826324

                    always_comb begin
                        temp1_ts1755007826321 = (inj_in1_1755007826321_412 + inj_in_1755007826311_513) * 10;
                        if (inj_sel_1755007826303_707) begin
                            temp2_ts1755007826321 = temp1_ts1755007826321 ^ (inj_in1_1755007826321_412 >>> 2);
                            inj_out1_1755007826321_203 = temp2_ts1755007826321 & inj_in_1755007826311_513;
                        end else begin
                            temp2_ts1755007826321 = temp1_ts1755007826321 | (inj_in_1755007826311_513 <<< 3);
                            inj_out1_1755007826321_203 = temp2_ts1755007826321 + inj_in1_1755007826321_412;
                        end
                        inj_out2_1755007826321_871 = temp1_ts1755007826321 - temp2_ts1755007826321;
                    end
                    // END: procedural_complex_ts1755007826321

                assign loop_wire1_ts1755007826319 = loop_wire2_ts1755007826319 | clk;
                assign loop_wire2_ts1755007826319 = loop_wire1_ts1755007826319; 
                assign inj_loop_out_1755007826319_758 = loop_wire1_ts1755007826319;
                // END: Comb_Loop_ts1755007826319

            assign intermediate_wire_ts1755007826317 = inj_uin_1755007826309_641 & inj_sel_1755007826303_707;
            always_comb begin
                if (intermediate_wire_ts1755007826317) begin
                    inj_out_c_1755007826316_419 = 1'b1;
                end else begin
                    inj_out_c_1755007826316_419 = 1'b0;
                end
            end
            // END: basic_assign_if_ts1755007826317

            // BEGIN: bind_directive_top_ts1755007826315
            target_module_for_bind target_inst(
                .i_target_clk   (clk),
                .i_target_data  (inj_i_target_data_1755007826303_598),
                .o_target_result(inj_o_result_1755007826315_981)
            );
            module_to_bind bind_inst(
                .i_bind_clk     (clk),
                .i_bind_control (inj_start_val_1755007826305_403),
                .o_bind_status  (inj_o_status_1755007826315_733)
            );
            // END: bind_directive_top_ts1755007826315

        assign internal_w_ts1755007826313 = inj_sel_1755007826303_707;
        assign inj_dout_1755007826313_54       = internal_w_ts1755007826313;
        // END: ContinuousWire_ts1755007826313

        module_assign_blocking module_assign_blocking_inst_1755007826312_7964 (
            .in_data(split_case_var_ts1755007826304),
            .out_valid_status(inj_out_valid_status_1755007826312_610)
        );
        // BEGIN: always_comb_assign_ts1755007826311
        always_comb begin
            inj_out_1755007826311_484 = inj_in_1755007826311_513;
        end
        // END: always_comb_assign_ts1755007826311

        // BEGIN: udnt_port_module_ts1755007826309
        assign inj_uout_1755007826309_471 = inj_uin_1755007826309_641;
        assign inj_udnt_output_1755007826309_362 = inj_sel_1755007826303_707;
        // END: udnt_port_module_ts1755007826309

        // BEGIN: LintParamUnused_ts1755007826308
        assign inj_out_n_1755007826308_261 = inj_sel_1755007826303_707;
        // END: LintParamUnused_ts1755007826308

        ModuleFF ModuleFF_inst_1755007826307_5045 (
            .reset(reset),
            .out1(inj_out1_1755007826307_848),
            .out2(inj_out2_1755007826307_625),
            .clk(clk),
            .in1(inj_in1_1755007826307_882),
            .in2(inj_in2_1755007826307_654)
        );
        // BEGIN: nested_module_ts1755007826306
        assign inj_nm_out_1755007826306_937 = inj_sel_1755007826303_707;
        // END: nested_module_ts1755007826306

        ReductionOperations ReductionOperations_inst_1755007826305_8380 (
            .or_reduce(inj_or_reduce_1755007826305_976),
            .xor_reduce(inj_xor_reduce_1755007826305_18),
            .data_in(inj_i_target_data_1755007826303_598),
            .and_reduce(inj_and_reduce_1755007826305_530)
        );
        loop_with_internal_assign loop_with_internal_assign_inst_1755007826305_8128 (
            .start_val(inj_start_val_1755007826305_403),
            .final_val(inj_final_val_1755007826305_716)
        );
    always_comb begin
        split_case_var_ts1755007826304 = 8'hFF;
        other_case_var_ts1755007826304 = 8'hAA;
        case (inj_sel_1755007826303_109)
            2'b00: begin
                split_case_var_ts1755007826304 = inj_i_target_data_1755007826303_598 + 5;
                other_case_var_ts1755007826304 = inj_i_target_data_1755007826303_598 + 6;
            end
            2'b01: begin
                split_case_var_ts1755007826304 = inj_i_target_data_1755007826303_598 - 5;
                other_case_var_ts1755007826304 = inj_i_target_data_1755007826303_598 - 6;
            end
            default: begin
                split_case_var_ts1755007826304 = inj_i_target_data_1755007826303_598;
                other_case_var_ts1755007826304 = inj_i_target_data_1755007826303_598;
            end
        endcase
        inj_out_case_a_1755007826303_402 = split_case_var_ts1755007826304;
        inj_out_case_b_1755007826303_549 = other_case_var_ts1755007826304;
    end
    // END: mod_split_case_ts1755007826304

    assign inj_out_val_1755007826303_161 = inj_i_target_data_1755007826303_598 + undeclared_var_ubddm;
    // END: used_before_declared_diag_mod_ts1755007826303

    always_comb inj_o_target_result_1755007826303_948 = inj_i_target_data_1755007826303_598 + 1;
    // END: target_module_for_bind_ts1755007826303

    ConditionalOps ConditionalOps_inst_1755007826303_9652 (
        .out_val(inj_out_val_1755007826303_130),
        .sel(inj_sel_1755007826303_707),
        .val_false(inj_val_false_1755007826303_540),
        .val_true(inj_val_true_1755007826303_119)
    );
endmodule

