interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module CombinationalLogicImplicit (
    input logic [3:0] a,
    input logic [3:0] b,
    output logic [3:0] sum
);
    always @* begin
        sum = a + b;
    end
endmodule

module basic_d_flipflop (
    input logic clk,
    input logic d,
    output logic q
);
    always_ff @(posedge clk) begin
        q <= d;
    end
endmodule

module module_forceable_attr (
    input wire i_clk,
    input logic i_data_in,
    input wire i_rst_n,
    input logic i_write_en,
    output logic o_forceable_signal,
    output logic o_read_signal
);
    logic forceable_signal ;
    logic read_internal;
    assign o_forceable_signal = forceable_signal;
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            forceable_signal <= 1'b0;
            read_internal <= 1'b0;
        end else begin
            if (i_write_en) begin
                forceable_signal <= i_data_in;
            end
            read_internal <= forceable_signal;
        end
    end
    assign o_read_signal = read_internal;
endmodule

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module module_case_write (
    input logic [7:0] data_case_a,
    input logic [7:0] data_case_b,
    input logic [1:0] select_case,
    output logic case_output_ready
);
    my_if case_vif_inst();
    always_comb begin
        case (select_case)
            2'b00: begin
                case_vif_inst.data = 8'hAA;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b0;
            end
            2'b01: begin
                case_vif_inst.data = data_case_a;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b1;
            end
            2'b10: begin
                case_vif_inst.data = data_case_b;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b1;
            end
            default: begin
                case_vif_inst.data = 8'hFF;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b0;
            end
        endcase
        case_output_ready = case_vif_inst.ready;
    end
endmodule

module split_if_empty_then (
    input logic clk_p,
    input logic condition_p,
    input logic [7:0] in_val_p,
    output logic [7:0] out_reg_p
);
    always @(posedge clk_p) begin
        if (condition_p) begin
        end else begin
            out_reg_p <= in_val_p;
        end
    end
endmodule

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_a_1755007902303_969,
    input logic [3:0] inj_b_1755007902303_730,
    input int inj_b_1755007902304_19,
    input logic [7:0] inj_data_case_b_1755007902305_941,
    input logic inj_i_reg_data_1755007902303_384,
    input logic inj_in1_bind_def_1755007902303_349,
    input logic [7:0] inj_in_1755007902305_780,
    input logic [15:0] inj_in_vector_1755007902303_864,
    input logic [2:0] inj_index_1755007902305_713,
    input logic [1:0] inj_select_case_1755007902305_730,
    input wire reset,
    output logic inj_case_output_ready_1755007902305_956,
    output logic [7:0] inj_data_out_fmt_1755007902307_453,
    output logic [7:0] inj_o1_r_1755007902318_416,
    output logic [7:0] inj_o2_r_1755007902318_192,
    output logic [7:0] inj_o3_r_1755007902318_362,
    output logic inj_o_forceable_signal_1755007902314_749,
    output logic inj_o_read_signal_1755007902314_192,
    output logic inj_o_reg_out_1755007902303_860,
    output logic [7:0] inj_o_result_1755007902311_974,
    output logic inj_o_status_1755007902311_986,
    output wire inj_o_wire_out_1755007902303_619,
    output logic inj_out1_bind_def_1755007902303_263,
    output logic inj_out_1755007902305_872,
    output logic inj_out_a_1755007902304_128,
    output int inj_out_b_1755007902304_568,
    output logic [7:0] inj_out_reg_cc_1755007902323_471,
    output logic [7:0] inj_out_reg_p_1755007902306_746,
    output logic [7:0] inj_out_slice_1755007902303_889,
    output logic inj_q_1755007902321_637,
    output logic [3:0] inj_sum_1755007902303_146
);
    // BEGIN: mod_basic_bind_ts1755007902303
    // BEGIN: nets_alias_clocking_ts1755007902303
    wire  w_internal_ts1755007902303;
    logic r_internal_ts1755007902303;
        // BEGIN: ModuleBasic_ts1755007902304
        parameter int P1  = 10;
        localparam int LP1 = 20;
        logic c_ts1755007902304;
        int   d_ts1755007902304;
        always_comb begin
            logic temp_v_ts1755007902304;
                // BEGIN: formatting_stress_ts1755007902309
                logic [7:0] temp_reg_fmt_ts1755007902309; 
                always_comb begin : stress_comb_block_label 
                    inj_data_out_fmt_1755007902307_453 = 8'hXX; 
                    if (temp_v_ts1755007902304) begin
                        if (r_internal_ts1755007902303) begin
                            case (inj_select_case_1755007902305_730) 
                                2'b00: inj_data_out_fmt_1755007902307_453 = inj_data_case_b_1755007902305_941;
                                2'b01: begin 
                                    inj_data_out_fmt_1755007902307_453 = ~inj_data_case_b_1755007902305_941; 
                                    end 
                                2'b10: begin 
                                    logic [7:0] added_val_ts1755007902309; 
                                        // BEGIN: split_complex_blocking_ts1755007902318
                                        logic [7:0] t1_r_ts1755007902318, t2_r_ts1755007902318;
                                            // BEGIN: split_conditional_reorder_ts1755007902323
                                            always @(posedge clk) begin
                                                inj_out_reg_cc_1755007902323_471 <= t2_r_ts1755007902318;
                                                if (temp_v_ts1755007902304) begin
                                                    inj_out_reg_cc_1755007902323_471 <= added_val_ts1755007902309;
                                                end else begin
                                                    inj_out_reg_cc_1755007902323_471 <= temp_reg_fmt_ts1755007902309;
                                                end
                                            end
                                            // END: split_conditional_reorder_ts1755007902323

                                            basic_d_flipflop basic_d_flipflop_inst_1755007902321_8988 (
                                                .clk(clk),
                                                .d(temp_v_ts1755007902304),
                                                .q(inj_q_1755007902321_637)
                                            );
                                        always @(*) begin
                                            t1_r_ts1755007902318 = temp_reg_fmt_ts1755007902309 + added_val_ts1755007902309;
                                            inj_o1_r_1755007902318_416 = t1_r_ts1755007902318 - inj_in_1755007902305_780;
                                            t2_r_ts1755007902318 = added_val_ts1755007902309 * inj_in_1755007902305_780;
                                            inj_o2_r_1755007902318_192 = t1_r_ts1755007902318 + t2_r_ts1755007902318;
                                            inj_o3_r_1755007902318_362 = t2_r_ts1755007902318 / 2;
                                        end
                                        // END: split_complex_blocking_ts1755007902318

                                        module_forceable_attr module_forceable_attr_inst_1755007902314_5184 (
                                            .i_write_en(inj_i_reg_data_1755007902303_384),
                                            .o_forceable_signal(inj_o_forceable_signal_1755007902314_749),
                                            .o_read_signal(inj_o_read_signal_1755007902314_192),
                                            .i_clk(clk),
                                            .i_data_in(inj_in1_bind_def_1755007902303_349),
                                            .i_rst_n(reset)
                                        );
                                        // BEGIN: bind_directive_top_ts1755007902312
                                        target_module_for_bind target_inst(
                                            .i_target_clk   (clk),
                                            .i_target_data  (added_val_ts1755007902309),
                                            .o_target_result(inj_o_result_1755007902311_974)
                                        );
                                        module_to_bind bind_inst(
                                            .i_bind_clk     (clk),
                                            .i_bind_control (inj_a_1755007902303_969),
                                            .o_bind_status  (inj_o_status_1755007902311_986)
                                        );
                                        // END: bind_directive_top_ts1755007902312

                                    added_val_ts1755007902309 = inj_data_case_b_1755007902305_941 + 8'h01; 
                                    inj_data_out_fmt_1755007902307_453 = added_val_ts1755007902309; 
                                    end 
                                default: inj_data_out_fmt_1755007902307_453 = 8'hFF; 
                            endcase 
                        end else begin
                            inj_data_out_fmt_1755007902307_453 = inj_data_case_b_1755007902305_941 - 8'h01; 
                        end 
                    end else begin
                        inj_data_out_fmt_1755007902307_453 = 8'h00; 
                    end 
                end
                // END: formatting_stress_ts1755007902309

                split_if_empty_then split_if_empty_then_inst_1755007902306_1519 (
                    .condition_p(inj_in1_bind_def_1755007902303_349),
                    .in_val_p(inj_in_1755007902305_780),
                    .out_reg_p(inj_out_reg_p_1755007902306_746),
                    .clk_p(clk)
                );
                module_case_write module_case_write_inst_1755007902305_5910 (
                    .select_case(inj_select_case_1755007902305_730),
                    .case_output_ready(inj_case_output_ready_1755007902305_956),
                    .data_case_a(inj_in_1755007902305_780),
                    .data_case_b(inj_data_case_b_1755007902305_941)
                );
                // BEGIN: variable_sel_mux_ts1755007902305
                assign inj_out_1755007902305_872 = inj_in_1755007902305_780[inj_index_1755007902305_713];
                // END: variable_sel_mux_ts1755007902305

            temp_v_ts1755007902304 = d_ts1755007902304;
            c_ts1755007902304      = temp_v_ts1755007902304;
        end
        assign inj_out_a_1755007902304_128 = inj_in1_bind_def_1755007902303_349;
        assign d_ts1755007902304     = inj_b_1755007902304_19;
        assign inj_out_b_1755007902304_568 = d_ts1755007902304 + P1 + LP1;
        // END: ModuleBasic_ts1755007902304

        // BEGIN: MiscExpressions_ValueRange_ts1755007902303
        always_comb begin
            inj_out_slice_1755007902303_889 = inj_in_vector_1755007902303_864[7:0];
        end
        // END: MiscExpressions_ValueRange_ts1755007902303

    assign w_internal_ts1755007902303  = reset & inj_i_reg_data_1755007902303_384;
    assign inj_o_wire_out_1755007902303_619  = w_internal_ts1755007902303;
    always_ff @(posedge clk) r_internal_ts1755007902303 <= inj_in1_bind_def_1755007902303_349;
    assign inj_o_reg_out_1755007902303_860 = r_internal_ts1755007902303;
    // END: nets_alias_clocking_ts1755007902303

    CombinationalLogicImplicit CombinationalLogicImplicit_inst_1755007902303_3407 (
        .sum(inj_sum_1755007902303_146),
        .a(inj_a_1755007902303_969),
        .b(inj_b_1755007902303_730)
    );
    assign inj_out1_bind_def_1755007902303_263 = ~inj_in1_bind_def_1755007902303_349;
    // END: mod_basic_bind_ts1755007902303
endmodule

