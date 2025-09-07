interface MyInterface (
    input logic clk
);
    logic req;
    logic valid;
    modport master (output req, input valid, input clk);
    modport slave (input req, output valid, input clk);
endinterface
interface seq2_if;
    logic [7:0] status_byte;
    modport PortB (output status_byte);
endinterface
interface seq_if;
    logic [31:0] value_a;
    modport PortA (output value_a);
endinterface
interface simple_if (
    input logic clk
);
    logic data;
    logic ready;
    modport master (output data, input ready);
    modport slave (input data, output ready);
endinterface
module ArrayIndexAndPartSelect (
    input logic [31:0] data_in,
    input int index_in,
    input logic [4:0] start_bit,
    output logic bit_out,
    output logic [7:0] byte_out
);
    logic [31:0] internal_data = data_in;
    assign bit_out = internal_data[index_in];
    assign byte_out = internal_data[start_bit +: 8];
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

module sequential_register (
    input logic clk,
    input logic data_in,
    input logic enable_in,
    input logic reset_n,
    output logic data_out
);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            data_out <= 1'b0; 
        end else if (enable_in) begin
            data_out <= data_in; 
        end
    end
endmodule

module shift_ops (
    input logic [7:0] data,
    input logic [2:0] shamt,
    output logic [7:0] left_shift,
    output logic [7:0] right_shift_arith,
    output logic [7:0] right_shift_logic
);
    assign left_shift = data << shamt;
    assign right_shift_logic = data >> shamt;
    assign right_shift_arith = data >>> shamt;
endmodule

module simple_assign (
    input logic [7:0] in,
    output logic [7:0] out
);
    assign out = in;
endmodule

module split_mixed_cond_seq (
    input logic clk_e,
    input logic condition_e,
    input logic [7:0] in_override_e,
    input logic [7:0] in_val_e,
    output logic [7:0] out_val_e,
    output logic status_e
);
    logic [7:0] temp_val_e;
    always @(posedge clk_e) begin
        temp_val_e <= in_val_e + 5;
        if (condition_e) begin
            out_val_e <= temp_val_e;
            status_e <= 1;
        end else begin
            out_val_e <= in_override_e;
            status_e <= 0;
        end
    end
endmodule

module sub_module (
    input logic sub_in,
    output logic sub_out
);
    assign sub_out = !sub_in;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_c_1755007876526_235,
    input logic [7:0] inj_data_in_1755007876525_711,
    input logic [31:0] inj_data_in_1755007876525_942,
    input logic inj_in2_1755007876529_910,
    input logic [7:0] inj_in4_dd_1755007876528_199,
    input int inj_index_in_1755007876525_749,
    input logic inj_main_in_1755007876526_987,
    input logic [2:0] inj_shamt_1755007876535_528,
    input logic [4:0] inj_start_bit_1755007876525_610,
    input wire reset,
    output logic inj_bit_out_1755007876525_863,
    output logic [7:0] inj_byte_out_1755007876525_687,
    output logic [7:0] inj_data_out_1755007876525_923,
    output logic inj_data_out_1755007876530_960,
    output logic [7:0] inj_inner_field_o_1755007876532_190,
    output logic [7:0] inj_left_shift_1755007876535_67,
    output logic inj_main_out_1755007876526_329,
    output logic [7:0] inj_out1_dd_1755007876528_236,
    output logic [7:0] inj_out2_dd_1755007876528_665,
    output logic [7:0] inj_out_1755007876526_163,
    output logic [7:0] inj_out_1755007876527_4,
    output logic inj_out_1755007876529_563,
    output logic [7:0] inj_out_val_e_1755007876537_911,
    output logic [7:0] inj_right_shift_arith_1755007876535_203,
    output logic [7:0] inj_right_shift_logic_1755007876535_636,
    output logic inj_sequence_valid_1755007876531_359,
    output logic inj_status_e_1755007876537_577,
    output logic inj_valid_out_1755007876534_481
);
    // BEGIN: SequentialLogic_ts1755007876525
    logic [7:0] internal_reg_ts1755007876525;
        split_mixed_cond_seq split_mixed_cond_seq_inst_1755007876537_2089 (
            .condition_e(inj_main_in_1755007876526_987),
            .in_override_e(inj_in4_dd_1755007876528_199),
            .in_val_e(inj_c_1755007876526_235),
            .out_val_e(inj_out_val_e_1755007876537_911),
            .status_e(inj_status_e_1755007876537_577),
            .clk_e(clk)
        );
        shift_ops shift_ops_inst_1755007876535_2419 (
            .right_shift_arith(inj_right_shift_arith_1755007876535_203),
            .right_shift_logic(inj_right_shift_logic_1755007876535_636),
            .data(inj_c_1755007876526_235),
            .shamt(inj_shamt_1755007876535_528),
            .left_shift(inj_left_shift_1755007876535_67)
        );
        // BEGIN: ModuleWithInterface_ts1755007876534
        MyInterface my_if (clk);
        assign my_if.req = 1'b1;
        assign inj_valid_out_1755007876534_481 = my_if.valid;
        // END: ModuleWithInterface_ts1755007876534

        // BEGIN: nested_types_mod_ts1755007876533
        typedef struct packed {
            logic [7:0] inner_field_ts1755007876532;
            logic [7:0] padding_ts1755007876532;
        } inner_struct_t;
        typedef union packed {
            logic [31:0] full_word_ts1755007876532;
            struct packed {
                logic [15:0] unused_ts1755007876532;
                inner_struct_t inner_data;
            } outer_fields;
        } outer_union_t;
        outer_union_t nested_var;
        always_comb begin
            nested_var.full_word_ts1755007876532 = inj_data_in_1755007876525_942;
        end
        assign inj_inner_field_o_1755007876532_190 = nested_var.outer_fields.inner_data.inner_field_ts1755007876532;
        // END: nested_types_mod_ts1755007876533

        module_sequence_different_if module_sequence_different_if_inst_1755007876531_401 (
            .sequence_valid(inj_sequence_valid_1755007876531_359),
            .input1(inj_data_in_1755007876525_942),
            .input2_byte(inj_data_in_1755007876525_711)
        );
        sequential_register sequential_register_inst_1755007876530_3467 (
            .clk(clk),
            .data_in(inj_in2_1755007876529_910),
            .enable_in(inj_main_in_1755007876526_987),
            .reset_n(reset),
            .data_out(inj_data_out_1755007876530_960)
        );
        // BEGIN: simple_and_gate_ts1755007876529
        assign inj_out_1755007876529_563 = inj_main_in_1755007876526_987 & inj_in2_1755007876529_910;
        // END: simple_and_gate_ts1755007876529

        // BEGIN: split_multi_nb_in_if_ts1755007876528
        always @(posedge clk) begin
            if (inj_main_in_1755007876526_987) begin
                inj_out1_dd_1755007876528_236 <= internal_reg_ts1755007876525 + inj_data_in_1755007876525_711;
                inj_out2_dd_1755007876528_665 <= inj_c_1755007876526_235 - inj_in4_dd_1755007876528_199;
            end else begin
                inj_out1_dd_1755007876528_236 <= internal_reg_ts1755007876525 * inj_data_in_1755007876525_711;
                inj_out2_dd_1755007876528_665 <= inj_c_1755007876526_235 / (inj_in4_dd_1755007876528_199 + 1);
            end
        end
        // END: split_multi_nb_in_if_ts1755007876528

        simple_assign simple_assign_inst_1755007876527_1300 (
            .out(inj_out_1755007876527_4),
            .in(internal_reg_ts1755007876525)
        );
        // BEGIN: deep_logic_ts1755007876526
        assign inj_out_1755007876526_163 = (((internal_reg_ts1755007876525 & inj_data_in_1755007876525_711) | (~inj_c_1755007876526_235)) ^ (internal_reg_ts1755007876525 + inj_data_in_1755007876525_711)) - (inj_c_1755007876526_235 << 2);
        // END: deep_logic_ts1755007876526

        // BEGIN: hierarchy_if_ts1755007876526
        sub_module u_sub (
            .sub_in(inj_main_in_1755007876526_987),
            .sub_out(inj_main_out_1755007876526_329)
        );
        simple_if if_inst (.clk(clk));
        always_comb begin
            if_inst.data = inj_main_in_1755007876526_987;
            if_inst.ready = inj_main_out_1755007876526_329;
        end
        // END: hierarchy_if_ts1755007876526

        ArrayIndexAndPartSelect ArrayIndexAndPartSelect_inst_1755007876525_8088 (
            .data_in(inj_data_in_1755007876525_942),
            .index_in(inj_index_in_1755007876525_749),
            .start_bit(inj_start_bit_1755007876525_610),
            .bit_out(inj_bit_out_1755007876525_863),
            .byte_out(inj_byte_out_1755007876525_687)
        );
    always @(posedge clk or negedge reset) begin
        if (~reset) begin
            internal_reg_ts1755007876525 <= 8'h00;
        end else begin
            internal_reg_ts1755007876525 <= inj_data_in_1755007876525_711;
        end
    end
    assign inj_data_out_1755007876525_923 = internal_reg_ts1755007876525;
    // END: SequentialLogic_ts1755007876525
endmodule

