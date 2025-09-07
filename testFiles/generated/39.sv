module ModuleBasic (
    input logic a,
    input int b,
    output logic out_a,
    output int out_b
);
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c;
    int   d;
    always_comb begin
        logic temp_v;
        temp_v = d;
        c      = temp_v;
    end
    assign out_a = a;
    assign d     = b;
    assign out_b = d + P1 + LP1;
endmodule

module ModuleHierarchy_High #(
    parameter int SEL_PARAM = 6
) (
    input logic [3:0] data_in,
    input int sel_in,
    output logic [7:0] data_out
);
    ModuleBasic m1 (
        .a      (1'b1),
        .b      (sel_in),
        .out_a  (),
        .out_b  ( )
    );
    if (SEL_PARAM > 5) begin : gen_high
        int high_data;
        ModuleBasic m_high (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (high_data)
        );
    end else begin : gen_low
        int low_data;
        ModuleBasic m_low (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (low_data)
        );
    end
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
        logic [1:0] sub_in;
        assign sub_in = data_in[i*2 +: 2];
        int temp_int;
        ModuleBasic m_inst (
            .a      (1'b0),
            .b      (int'(sub_in)),
            .out_a  (),
            .out_b  (temp_int)
        );
        assign data_out[i*4 +: 4] = temp_int[3:0];
    end
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_data_in_1755004216402_151,
    input logic [31:0] inj_in_vec_1755004216401_560,
    input int inj_start_index_1755004216401_472,
    input int inj_width_1755004216401_755,
    input wire reset,
    output logic [7:0] inj_data_out_1755004216402_255,
    output logic [7:0] inj_out_down_1755004216401_627,
    output logic [7:0] inj_out_up_1755004216401_408
);
    // BEGIN: range_select_indexed_packed_ts1755004216402
    ModuleHierarchy_High ModuleHierarchy_High_inst_1755004216402_3816 (
        .data_in(inj_data_in_1755004216402_151),
        .sel_in(inj_start_index_1755004216401_472),
        .data_out(inj_data_out_1755004216402_255)
    );
    always_comb begin
        if (inj_start_index_1755004216401_472 >= 0 && inj_width_1755004216401_755 > 0 && inj_start_index_1755004216401_472 + inj_width_1755004216401_755 <= 32) begin
            case (inj_width_1755004216401_755)
                1: inj_out_up_1755004216401_408 = inj_in_vec_1755004216401_560[inj_start_index_1755004216401_472 +: 1];
                2: inj_out_up_1755004216401_408 = inj_in_vec_1755004216401_560[inj_start_index_1755004216401_472 +: 2];
                4: inj_out_up_1755004216401_408 = inj_in_vec_1755004216401_560[inj_start_index_1755004216401_472 +: 4];
                8: inj_out_up_1755004216401_408 = inj_in_vec_1755004216401_560[inj_start_index_1755004216401_472 +: 8];
                default: inj_out_up_1755004216401_408 = 'x;
            endcase
        end else begin
            inj_out_up_1755004216401_408 = 'x;
        end
        if (inj_start_index_1755004216401_472 >= inj_width_1755004216401_755 - 1 && inj_width_1755004216401_755 > 0 && inj_start_index_1755004216401_472 < 32) begin
            case (inj_width_1755004216401_755)
                1: inj_out_down_1755004216401_627 = inj_in_vec_1755004216401_560[inj_start_index_1755004216401_472 -: 1];
                2: inj_out_down_1755004216401_627 = inj_in_vec_1755004216401_560[inj_start_index_1755004216401_472 -: 2];
                4: inj_out_down_1755004216401_627 = inj_in_vec_1755004216401_560[inj_start_index_1755004216401_472 -: 4];
                8: inj_out_down_1755004216401_627 = inj_in_vec_1755004216401_560[inj_start_index_1755004216401_472 -: 8];
                default: inj_out_down_1755004216401_627 = 'x;
            endcase
        end else begin
            inj_out_down_1755004216401_627 = 'x;
        end
    end
    // END: range_select_indexed_packed_ts1755004216402
endmodule

