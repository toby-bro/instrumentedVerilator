module module_in_program_ref (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module range_select_indexed_packed (
    input logic [31:0] in_vec,
    input int start_index,
    input int width,
    output logic [7:0] out_down,
    output logic [7:0] out_up
);
    always_comb begin
        if (start_index >= 0 && width > 0 && start_index + width <= 32) begin
            case (width)
                1: out_up = in_vec[start_index +: 1];
                2: out_up = in_vec[start_index +: 2];
                4: out_up = in_vec[start_index +: 4];
                8: out_up = in_vec[start_index +: 8];
                default: out_up = 'x;
            endcase
        end else begin
            out_up = 'x;
        end
        if (start_index >= width - 1 && width > 0 && start_index < 32) begin
            case (width)
                1: out_down = in_vec[start_index -: 1];
                2: out_down = in_vec[start_index -: 2];
                4: out_down = in_vec[start_index -: 4];
                8: out_down = in_vec[start_index -: 8];
                default: out_down = 'x;
            endcase
        end else begin
            out_down = 'x;
        end
    end
endmodule

module snippet (
    input wire clk,
    input int inj_in_val_1755004209042_118,
    input logic [31:0] inj_in_vec_1755004209042_190,
    input int inj_width_1755004209042_394,
    input wire reset,
    output logic [7:0] inj_out_down_1755004209042_454,
    output logic [7:0] inj_out_up_1755004209042_264,
    output int inj_out_val_1755004209042_416
);
    range_select_indexed_packed range_select_indexed_packed_inst_1755004209042_5955 (
        .out_down(inj_out_down_1755004209042_454),
        .out_up(inj_out_up_1755004209042_264),
        .in_vec(inj_in_vec_1755004209042_190),
        .start_index(inj_in_val_1755004209042_118),
        .width(inj_width_1755004209042_394)
    );
    module_in_program_ref module_in_program_ref_inst_1755004209042_3883 (
        .in_val(inj_in_val_1755004209042_118),
        .out_val(inj_out_val_1755004209042_416)
    );
endmodule

