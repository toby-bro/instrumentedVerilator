module LintImplicitWidth (
    input logic [7:0] in_wide,
    output logic [3:0] out_narrow
);
    assign out_narrow = in_wide;
endmodule

module module_bitfield_concat (
    input wire clk,
    input logic [7:0] input_bf,
    input logic [3:0] input_bf_slice,
    input wire rst,
    output logic [3:0] inj_out_narrow_1755538616659_625,
    output logic [7:0] output_bf,
    output logic [3:0] output_bf_slice
);
    logic [7:0] my_bitfield ;
        LintImplicitWidth LintImplicitWidth_inst_1755538616659_2740 (
            .in_wide(my_bitfield),
            .out_narrow(inj_out_narrow_1755538616659_625)
        );
    always_comb begin
        if (input_bf[7]) begin
            my_bitfield = input_bf;
        end else begin
            my_bitfield = {input_bf[0], input_bf[7:1]};
        end
        my_bitfield[3:0] = input_bf_slice;
    end
    assign output_bf = my_bitfield;
    assign output_bf_slice = my_bitfield[3:0];
endmodule

