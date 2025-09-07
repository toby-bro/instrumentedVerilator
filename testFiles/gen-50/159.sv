interface struct_if;
    logic [7:0] packet_field1;
    logic [7:0] packet_field2;
    logic tx_en;
    modport Access (output packet_field1, output packet_field2, output tx_en);
endinterface
module Comb_Assign (
    input wire in1,
    input wire in2,
    output wire out
);
    assign out = in1 & in2;
endmodule

module LintSensitiveList (
    input logic in_p,
    input logic in_q,
    output logic out_r
);
    always_comb begin
        out_r = in_p | in_q;
    end
endmodule

module SequentialLogic (
    input logic clk,
    input logic [7:0] data_in,
    input logic rst,
    output logic [7:0] data_out
);
    logic [7:0] internal_reg;
    always @(posedge clk or negedge rst) begin
        if (~rst) begin
            internal_reg <= 8'h00;
        end else begin
            internal_reg <= data_in;
        end
    end
    assign data_out = internal_reg;
endmodule

module SimpleAssign (
    input logic [9:0] val_in,
    output logic [9:0] val_out
);
    assign val_out = val_in;
endmodule

module part_select_ops (
    input wire [31:0] wide_in,
    output wire [7:0] lower_byte_out,
    output wire [7:0] upper_byte_out
);
    wire [31:0] processed_wide;
    assign processed_wide = wide_in * 2;
    assign upper_byte_out = processed_wide[31:24];
    assign lower_byte_out = processed_wide[7:0];
endmodule

module module_struct_write (
    input logic [7:0] in_field1,
    input logic [7:0] in_field2,
    output logic tx_status
);
    struct_if stif_inst();
    always_comb begin
        stif_inst.packet_field1 = in_field1;
        stif_inst.packet_field2 = in_field2;
        stif_inst.tx_en = 1'b1;
        tx_status = stif_inst.tx_en;
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
    input bit [7:0] inj_data_in_1755007806378_901,
    input logic [7:0] inj_in_1755007806375_742,
    input logic [15:0] inj_in_1755007806376_54,
    input logic [7:0] inj_in_field2_1755007806375_328,
    input logic inj_in_p_1755007806376_762,
    input logic inj_in_q_1755007806376_63,
    input logic [2:0] inj_index_1755007806375_652,
    input bit inj_select_signal_1755007806378_913,
    input logic [9:0] inj_val_in_1755007806377_882,
    input wire [31:0] inj_wide_in_1755007806379_470,
    input wire reset,
    output bit [7:0] inj_data_out_1755007806378_29,
    output logic [7:0] inj_data_out_1755007806378_607,
    output wire [7:0] inj_lower_byte_out_1755007806379_245,
    output logic inj_o_out_1755007806380_939,
    output logic [7:0] inj_out1_a_1755007806377_439,
    output logic inj_out_1755007806375_965,
    output logic [15:0] inj_out_1755007806376_516,
    output wire inj_out_1755007806376_984,
    output logic [7:0] inj_out_1755007806383_47,
    output logic [7:0] inj_out_data_1755007806375_61,
    output logic [3:0] inj_out_narrow_1755007806383_179,
    output logic inj_out_r_1755007806376_779,
    output logic inj_tx_status_1755007806375_332,
    output wire [7:0] inj_upper_byte_out_1755007806379_18,
    output logic [9:0] inj_val_out_1755007806377_188
);
    // BEGIN: SimpleAssign_ts1755007806375
    // BEGIN: always_comb_assign_ts1755007806376
    // BEGIN: split_basic_blocking_ts1755007806377
    // BEGIN: SimpleLogicTest_ts1755007806379
    logic [7:0] temp_data_ts1755007806379;
        // BEGIN: deep_logic_ts1755007806384
        assign inj_out_1755007806383_47 = (((temp_data_ts1755007806379 & inj_in_field2_1755007806375_328) | (~inj_in_1755007806375_742)) ^ (temp_data_ts1755007806379 + inj_in_field2_1755007806375_328)) - (inj_in_1755007806375_742 << 2);
        // END: deep_logic_ts1755007806384

        // BEGIN: LintImplicitWidth_ts1755007806383
        assign inj_out_narrow_1755007806383_179 = inj_in_field2_1755007806375_328;
        // END: LintImplicitWidth_ts1755007806383

        // BEGIN: extern_declarations_ts1755007806380
        assign inj_o_out_1755007806380_939 = inj_in_q_1755007806376_63;
        // END: extern_declarations_ts1755007806380

        part_select_ops part_select_ops_inst_1755007806379_7648 (
            .lower_byte_out(inj_lower_byte_out_1755007806379_245),
            .upper_byte_out(inj_upper_byte_out_1755007806379_18),
            .wide_in(inj_wide_in_1755007806379_470)
        );
    always_comb begin
        if (inj_select_signal_1755007806378_913) begin
            temp_data_ts1755007806379 = inj_data_in_1755007806378_901 + 1;
        end else begin
            temp_data_ts1755007806379 = inj_data_in_1755007806378_901 - 1;
        end
        inj_data_out_1755007806378_29 = temp_data_ts1755007806379;
    end
    // END: SimpleLogicTest_ts1755007806379

    SequentialLogic SequentialLogic_inst_1755007806378_7928 (
        .data_in(inj_in_1755007806375_742),
        .rst(reset),
        .data_out(inj_data_out_1755007806378_607),
        .clk(clk)
    );
    always @(*) begin
        inj_out1_a_1755007806377_439 = inj_in_field2_1755007806375_328;
    end
    // END: split_basic_blocking_ts1755007806377

    SimpleAssign SimpleAssign_inst_1755007806377_2085 (
        .val_out(inj_val_out_1755007806377_188),
        .val_in(inj_val_in_1755007806377_882)
    );
    always_comb begin
        inj_out_1755007806376_516 = inj_in_1755007806376_54;
    end
    // END: always_comb_assign_ts1755007806376

    Comb_Assign Comb_Assign_inst_1755007806376_1854 (
        .in1(clk),
        .in2(reset),
        .out(inj_out_1755007806376_984)
    );
    LintSensitiveList LintSensitiveList_inst_1755007806376_3572 (
        .in_p(inj_in_p_1755007806376_762),
        .in_q(inj_in_q_1755007806376_63),
        .out_r(inj_out_r_1755007806376_779)
    );
    assign inj_out_data_1755007806375_61 = inj_in_1755007806375_742;
    // END: SimpleAssign_ts1755007806375

    module_struct_write module_struct_write_inst_1755007806375_254 (
        .in_field1(inj_in_1755007806375_742),
        .in_field2(inj_in_field2_1755007806375_328),
        .tx_status(inj_tx_status_1755007806375_332)
    );
    variable_sel_mux variable_sel_mux_inst_1755007806375_4656 (
        .out(inj_out_1755007806375_965),
        .in(inj_in_1755007806375_742),
        .index(inj_index_1755007806375_652)
    );
endmodule

