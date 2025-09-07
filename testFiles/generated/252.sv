interface seq2_if;
    logic [7:0] status_byte;
    modport PortB (output status_byte);
endinterface
interface seq_if;
    logic [31:0] value_a;
    modport PortA (output value_a);
endinterface
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

module PragmaProtectOptions (
    input int config_data_in,
    output int config_data_out
);
`ifdef SLANG_PRAGMA
`protect encoding (enctype="base64", line_length=76, bytes=1024)
`endif
`ifdef SLANG_PRAGMA
`protect license (library="my_project_lib", entry="start_feature_A", match=42, feature="feature_set_B", exit="end_feature_A")
`endif
`ifdef SLANG_PRAGMA
`protect reset
`endif
`ifdef SLANG_PRAGMA
`protect viewport (object="design.module_a.instance_b.register_c", access="read-only")
`endif
assign config_data_out = config_data_in + 1;
endmodule

module snippet (
    input wire clk,
    input int inj_config_data_in_1755007838438_973,
    input logic [7:0] inj_data_in_1755007838436_500,
    input wire [31:0] inj_data_in_1755007838442_679,
    input logic [3:0] inj_i_bind_control_1755007838435_680,
    input bit [3:0] inj_in1_1755007838436_534,
    input bit [3:0] inj_in2_1755007838436_73,
    input logic inj_in_a_1755007838435_923,
    input wire [3:0] inj_in_a_1755007838444_488,
    input wire [3:0] inj_in_b_1755007838444_693,
    input wire [7:0] inj_in_c_1755007838444_105,
    input wire reset,
    output int inj_config_data_out_1755007838438_137,
    output wire inj_data_d_1755007838436_612,
    output logic [31:0] inj_data_out_1755007838442_145,
    output logic [7:0] inj_data_out_1755007838446_791,
    output logic inj_o_bind_status_1755007838435_819,
    output bit [3:0] inj_out1_1755007838436_967,
    output logic [7:0] inj_out1_a_1755007838450_917,
    output bit [3:0] inj_out2_1755007838436_730,
    output logic inj_out_a_1755007838435_407,
    output logic [15:0] inj_out_concat_1755007838444_624,
    output wire [7:0] inj_out_data_1755007838458_828,
    output logic [7:0] inj_out_if_else_1755007838444_890,
    output logic [7:0] inj_out_nested_a_1755007838436_643,
    output logic [7:0] inj_out_nested_b_1755007838436_968,
    output logic [7:0] inj_out_val_c_1755007838455_871,
    output logic inj_out_valid_1755007838448_854,
    output logic inj_reset_1755007838441_194,
    output logic inj_sequence_valid_1755007838452_58
);
    // BEGIN: module_to_bind_ts1755007838435
    // BEGIN: mod_name_conflict_ts1755007838435
    logic conflict_var_ts1755007838435;
        // BEGIN: mod_split_nested_ts1755007838437
        logic [7:0]  split_nested_var_ts1755007838437;
        logic [7:0] other_nested_var_ts1755007838437;
            // BEGIN: cu_timeunit_mod_ts1755007838441
            logic internal_sig_ts1755007838441;
                // BEGIN: mod_part_select_ts1755007838442
                logic [31:0] temp_reg_ts1755007838442;
                    // BEGIN: ModuleImplicitPort_ts1755007838448
                    logic valid_ts1755007838448;
                        // BEGIN: split_seq_dependency_ts1755007838455
                        logic [7:0] mid_val_c_ts1755007838455;
                            // BEGIN: simple_comb_ts1755007838458
                            wire [7:0] intermediate_a_ts1755007838458;
                            wire [7:0] intermediate_b_ts1755007838458;
                            wire [7:0] intermediate_c_ts1755007838458;
                            assign intermediate_a_ts1755007838458 = inj_in_c_1755007838444_105 + 8'd1;
                            assign intermediate_b_ts1755007838458 = intermediate_a_ts1755007838458 << 1;
                            assign intermediate_c_ts1755007838458 = intermediate_a_ts1755007838458 >> 1;
                            assign inj_out_data_1755007838458_828 = intermediate_b_ts1755007838458 | intermediate_c_ts1755007838458;
                            // END: simple_comb_ts1755007838458

                        always @(posedge clk) begin
                            mid_val_c_ts1755007838455 <= inj_data_in_1755007838436_500 + 1;
                            inj_out_val_c_1755007838455_871 <= mid_val_c_ts1755007838455 * 2;
                        end
                        // END: split_seq_dependency_ts1755007838455

                        // BEGIN: module_sequence_different_if_ts1755007838453
                        seq_if sif_port();
                        seq2_if sif2_port();
                        always_comb begin
                            sif_port.value_a = temp_reg_ts1755007838442;
                            sif2_port.status_byte = other_nested_var_ts1755007838437;
                            inj_sequence_valid_1755007838452_58 = 1'b1;
                        end
                        // END: module_sequence_different_if_ts1755007838453

                        // BEGIN: split_basic_blocking_ts1755007838450
                        always @(*) begin
                            inj_out1_a_1755007838450_917 = other_nested_var_ts1755007838437;
                        end
                        // END: split_basic_blocking_ts1755007838450

                    assign valid_ts1755007838448 = |split_nested_var_ts1755007838437;
                    assign inj_out_valid_1755007838448_854 = valid_ts1755007838448;
                    // END: ModuleImplicitPort_ts1755007838448

                    // BEGIN: cu_base_ts1755007838446
                    assign inj_data_out_1755007838446_791 = split_nested_var_ts1755007838437;
                    // END: cu_base_ts1755007838446

                    // BEGIN: module_concat_if_ts1755007838444
                    always_comb begin
                    inj_out_concat_1755007838444_624 = {inj_in_a_1755007838444_488, inj_in_b_1755007838444_693, inj_in_c_1755007838444_105};
                    if (clk) begin
                        inj_out_if_else_1755007838444_890 = inj_in_c_1755007838444_105;
                    end else begin
                        inj_out_if_else_1755007838444_890 = {inj_in_a_1755007838444_488, inj_in_b_1755007838444_693};
                    end
                    end
                    // END: module_concat_if_ts1755007838444

                always_comb begin
                    temp_reg_ts1755007838442[7:0] = inj_data_in_1755007838442_679[7:0];
                    temp_reg_ts1755007838442[15:8] = inj_data_in_1755007838442_679[23:16];
                    temp_reg_ts1755007838442[31:16] = inj_data_in_1755007838442_679[15:0];
                    temp_reg_ts1755007838442[0] = inj_data_in_1755007838442_679[31];
                    temp_reg_ts1755007838442[8] = inj_data_in_1755007838442_679[0];
                    inj_data_out_1755007838442_145 = temp_reg_ts1755007838442;
                end
                // END: mod_part_select_ts1755007838442

            always_ff @(posedge clk) begin
                inj_reset_1755007838441_194 <= 1'b0;
                internal_sig_ts1755007838441 = clk;
            end
            // END: cu_timeunit_mod_ts1755007838441

            PragmaProtectOptions PragmaProtectOptions_inst_1755007838438_9934 (
                .config_data_in(inj_config_data_in_1755007838438_973),
                .config_data_out(inj_config_data_out_1755007838438_137)
            );
        always_ff @(posedge clk or posedge reset) begin
            if (reset) begin
                split_nested_var_ts1755007838437 <= 8'b0;
                other_nested_var_ts1755007838437 <= 8'b0;
            end else begin
                split_nested_var_ts1755007838437 <= 8'h11; 
                other_nested_var_ts1755007838437 <= 8'h22; 
                if (conflict_var_ts1755007838435) begin
                    split_nested_var_ts1755007838437 <= inj_data_in_1755007838436_500 + 10;
                    other_nested_var_ts1755007838437 <= inj_data_in_1755007838436_500 + 20;
                    if (inj_in_a_1755007838435_923) begin
                        split_nested_var_ts1755007838437 <= inj_data_in_1755007838436_500 + 100;
                        other_nested_var_ts1755007838437 <= inj_data_in_1755007838436_500 + 200;
                    end
                end else begin
                    split_nested_var_ts1755007838437 <= inj_data_in_1755007838436_500 - 10;
                    other_nested_var_ts1755007838437 <= inj_data_in_1755007838436_500 - 20;
                end
            end
        end
        always_comb begin
            inj_out_nested_a_1755007838436_643 = split_nested_var_ts1755007838437;
            inj_out_nested_b_1755007838436_968 = other_nested_var_ts1755007838437;
        end
        // END: mod_split_nested_ts1755007838437

        // BEGIN: simple_logic_b_ts1755007838436
        assign inj_data_d_1755007838436_612 = clk;
        // END: simple_logic_b_ts1755007838436

        ModuleFF ModuleFF_inst_1755007838436_4084 (
            .out2(inj_out2_1755007838436_730),
            .clk(clk),
            .in1(inj_in1_1755007838436_534),
            .in2(inj_in2_1755007838436_73),
            .reset(reset),
            .out1(inj_out1_1755007838436_967)
        );
    parameter int conflict_param = 1;
    assign inj_out_a_1755007838435_407 = inj_in_a_1755007838435_923;
    // END: mod_name_conflict_ts1755007838435

    always_comb inj_o_bind_status_1755007838435_819 = |inj_i_bind_control_1755007838435_680;
    // END: module_to_bind_ts1755007838435
endmodule

