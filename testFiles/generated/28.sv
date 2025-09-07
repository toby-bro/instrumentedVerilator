interface seq2_if;
    logic [7:0] status_byte;
    modport PortB (output status_byte);
endinterface
interface seq_if;
    logic [31:0] value_a;
    modport PortA (output value_a);
endinterface
module coalesced_assign (
    input logic [3:0] in_h,
    input logic [3:0] in_l,
    output logic [7:0] out
);
    wire [7:0] temp_wire;
    assign temp_wire[7:4] = in_h;
    assign temp_wire[3:0] = in_l;
    assign out = temp_wire;
endmodule

module module_sequence_different_if (
    input logic [31:0] input1,
    input logic [7:0] input2_byte,
    output logic sequence_valid
);
    seq_if sif_port();
    seq2_if sif2_port();
    always_comb begin
        sif_port.value_a = input1;
        sif2_port.status_byte = input2_byte;
        sequence_valid = 1'b1;
    end
endmodule

module variable_sel_mux (
    input logic [7:0] in,
    input logic [2:0] index,
    output logic out
);
    assign out = in[index];
endmodule

module snippet (
    input wire clk,
    input wire [2:0] inj_count_in_1755004212468_659,
    input logic [7:0] inj_d1_1755004212464_775,
    input logic [7:0] inj_d2_1755004212464_475,
    input logic [7:0] inj_d3_1755004212464_788,
    input logic [15:0] inj_dividend_mod_1755004212469_858,
    input logic [3:0] inj_flags_1755004212464_803,
    input int inj_i_val_1755004212466_60,
    input logic [3:0] inj_in_l_1755004212476_778,
    input logic [1:0] inj_in_val_1755004212478_30,
    input logic [31:0] inj_input1_1755004212471_883,
    input logic [15:0] inj_numerator_1755004212469_554,
    input logic [2:0] inj_shamt_1755004212470_59,
    input wire reset,
    output wire [2:0] inj_count_out_1755004212468_516,
    output logic [7:0] inj_left_shift_1755004212470_960,
    output logic inj_o_attr_out_1755004212473_537,
    output int inj_o_val_1755004212466_927,
    output logic [7:0] inj_out1_1755004212464_146,
    output logic inj_out_1755004212472_736,
    output logic [7:0] inj_out_1755004212476_660,
    output logic inj_out_a_1755004212475_891,
    output int inj_out_b_1755004212475_71,
    output logic [7:0] inj_out_field_a_1755004212474_231,
    output logic [7:0] inj_out_field_b_1755004212474_478,
    output reg inj_out_res_1755004212478_283,
    output logic [15:0] inj_quotient_1755004212469_974,
    output logic [7:0] inj_remainder_1755004212469_469,
    output logic [7:0] inj_right_shift_arith_1755004212470_476,
    output logic [7:0] inj_right_shift_logic_1755004212470_259,
    output logic inj_sequence_valid_1755004212471_69
);
    // BEGIN: dup_logic_ops_ts1755004212466
    logic cond1_ts1755004212465, cond2_ts1755004212465, cond3_ts1755004212465;
    logic complex_cond1_ts1755004212465, complex_cond2_ts1755004212465;
        // BEGIN: mod_automatic_task_ts1755004212466
        task automatic update_val(input int in_v, output int out_v);
            out_v = in_v * 2;
        endtask
        always_comb begin
            int temp_val_ts1755004212466;
                // BEGIN: simple_seq_ts1755004212469
                reg [2:0] counter_reg_ts1755004212469;
                    // BEGIN: ModuleBasic_ts1755004212475
                    parameter int P1  = 10;
                    localparam int LP1 = 20;
                    logic c_ts1755004212475;
                    int   d_ts1755004212475;
                    always_comb begin
                        logic temp_v_ts1755004212475;
                            // BEGIN: case_basic_ts1755004212478
                            always_comb begin
                                inj_out_res_1755004212478_283 = 1'b0;
                                case (inj_in_val_1755004212478_30)
                                    2'b00: inj_out_res_1755004212478_283 = 1'b0;
                                    2'b01: inj_out_res_1755004212478_283 = 1'b1;
                                    2'b10: inj_out_res_1755004212478_283 = 1'b0;
                                    2'b11: inj_out_res_1755004212478_283 = 1'b1;
                                endcase
                            end
                            // END: case_basic_ts1755004212478

                            coalesced_assign coalesced_assign_inst_1755004212476_6547 (
                                .in_h(inj_flags_1755004212464_803),
                                .in_l(inj_in_l_1755004212476_778),
                                .out(inj_out_1755004212476_660)
                            );
                        temp_v_ts1755004212475 = d_ts1755004212475;
                        c_ts1755004212475      = temp_v_ts1755004212475;
                    end
                    assign inj_out_a_1755004212475_891 = cond1_ts1755004212465;
                    assign d_ts1755004212475     = temp_val_ts1755004212466;
                    assign inj_out_b_1755004212475_71 = d_ts1755004212475 + P1 + LP1;
                    // END: ModuleBasic_ts1755004212475

                    // BEGIN: StructExample_ts1755004212474
                    typedef struct packed {
                        logic [7:0] field_a_ts1755004212474;
                        logic [7:0] field_b_ts1755004212474;
                    } example_struct_t;
                    example_struct_t my_struct;
                    always_comb begin
                        my_struct     = inj_dividend_mod_1755004212469_858;
                        inj_out_field_a_1755004212474_231   = my_struct.field_a_ts1755004212474;
                        inj_out_field_b_1755004212474_478   = my_struct.field_b_ts1755004212474;
                    end
                    // END: StructExample_ts1755004212474

                    // BEGIN: attributes_test_ts1755004212473
                    (* synthesis_preserve *) logic internal_signal;
                    always_comb begin : my_combinational_block
                        internal_signal = cond1_ts1755004212465 ? 1'b1 : 1'b0;
                        inj_o_attr_out_1755004212473_537      = internal_signal;
                    end
                    // END: attributes_test_ts1755004212473

                    variable_sel_mux variable_sel_mux_inst_1755004212472_7284 (
                        .in(inj_d3_1755004212464_788),
                        .index(inj_shamt_1755004212470_59),
                        .out(inj_out_1755004212472_736)
                    );
                    module_sequence_different_if module_sequence_different_if_inst_1755004212471_6147 (
                        .input2_byte(inj_d2_1755004212464_475),
                        .sequence_valid(inj_sequence_valid_1755004212471_69),
                        .input1(inj_input1_1755004212471_883)
                    );
                    // BEGIN: shift_ops_ts1755004212470
                    assign inj_left_shift_1755004212470_960 = inj_d2_1755004212464_475 << inj_shamt_1755004212470_59;
                    assign inj_right_shift_logic_1755004212470_259 = inj_d2_1755004212464_475 >> inj_shamt_1755004212470_59;
                    assign inj_right_shift_arith_1755004212470_476 = inj_d2_1755004212464_475 >>> inj_shamt_1755004212470_59;
                    // END: shift_ops_ts1755004212470

                    // BEGIN: div_mod_ops_ts1755004212469
                    assign inj_quotient_1755004212469_974 = (inj_d1_1755004212464_775 == 0) ? 16'hFFFF : (inj_numerator_1755004212469_554 / inj_d1_1755004212464_775); 
                    assign inj_remainder_1755004212469_469 = (inj_d2_1755004212464_475 == 0) ? 8'hFF : (inj_dividend_mod_1755004212469_858 % inj_d2_1755004212464_475);
                    // END: div_mod_ops_ts1755004212469

                always @(posedge clk or posedge reset) begin
                    if (reset) begin
                        counter_reg_ts1755004212469 <= 3'b000;
                    end else begin
                        counter_reg_ts1755004212469 <= inj_count_in_1755004212468_659 + 3'b001;
                    end
                end
                assign inj_count_out_1755004212468_516 = counter_reg_ts1755004212469;
                // END: simple_seq_ts1755004212469

            update_val(inj_i_val_1755004212466_60, temp_val_ts1755004212466);
            inj_o_val_1755004212466_927 = temp_val_ts1755004212466;
        end
        // END: mod_automatic_task_ts1755004212466

    assign cond1_ts1755004212465 = inj_flags_1755004212464_803[0] && inj_flags_1755004212464_803[1];
    assign cond2_ts1755004212465 = inj_flags_1755004212464_803[2] || inj_flags_1755004212464_803[3];
    assign cond3_ts1755004212465 = !inj_flags_1755004212464_803[0];
    assign complex_cond1_ts1755004212465 = (cond1_ts1755004212465 || cond2_ts1755004212465) && cond3_ts1755004212465;
    assign complex_cond2_ts1755004212465 = !(inj_flags_1755004212464_803[0] && inj_flags_1755004212464_803[1]) || (inj_flags_1755004212464_803[2] || !inj_flags_1755004212464_803[3]);
    always_comb begin
        inj_out1_1755004212464_146 = '0;
        if (complex_cond1_ts1755004212465) begin
            inj_out1_1755004212464_146 = inj_d1_1755004212464_775 + inj_d2_1755004212464_475;
        end else begin
            inj_out1_1755004212464_146 = inj_d1_1755004212464_775 ^ inj_d3_1755004212464_788;
        end
        if (complex_cond2_ts1755004212465) begin
            inj_out1_1755004212464_146 = inj_out1_1755004212464_146 + inj_d3_1755004212464_788;
        end else begin
            inj_out1_1755004212464_146 = inj_out1_1755004212464_146 - inj_d3_1755004212464_788;
        end
        if ((inj_flags_1755004212464_803[0] && inj_flags_1755004212464_803[1]) && (!inj_flags_1755004212464_803[2] || inj_flags_1755004212464_803[3])) begin
            inj_out1_1755004212464_146 = inj_out1_1755004212464_146 * 2;
        end
    end
    // END: dup_logic_ops_ts1755004212466
endmodule

