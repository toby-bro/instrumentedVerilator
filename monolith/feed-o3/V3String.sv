module str_escape_mod #(parameter string TEXT = "Line1\nLine2\rLine3\t\v\a\f\\%%\x41\101") (
    input  logic in_sig,
    output logic out_sig
);
    assign out_sig = in_sig;
endmodule
module real_underscore_mod #(parameter real SCALE = 1_234.56_78) (
    input  logic       clk,
    output logic [31:0] result
);
    assign result = $rtoi(SCALE);
endmodule
module attribute_case_mod (
    input  logic [7:0] din,
    output logic [7:0] dout
);
    (* My_Attribute = "BaR" *)
    assign dout = din;
endmodule
module long_identifier_mod (
    input  logic i,
    output logic o
);
    logic [7:0] extremely_long_identifier_signal_name_with_many_parts_and_segments_to_trigger_internal_name_processing_algorithms_in_verilator___________________________part2;
    logic dummy_signal_with_really_really_really_really_really_really_really_really_really_really_really_really_really_really_really_really_really_really_really_really_long_name_to_test_hashing_mechanism_of_verilator;
    assign extremely_long_identifier_signal_name_with_many_parts_and_segments_to_trigger_internal_name_processing_algorithms_in_verilator___________________________part2 = 8'hA5;
    assign dummy_signal_with_really_really_really_really_really_really_really_really_really_really_really_really_really_really_really_really_really_really_really_really_long_name_to_test_hashing_mechanism_of_verilator = 1'b0;
    assign o = i;
endmodule
module generate_case_mod #(parameter int WIDTH = 5) (
    input  logic [WIDTH-1:0] in_bus,
    output logic [WIDTH-1:0] out_bus
);
    genvar idx;
    generate
        for (idx = 0; idx < WIDTH; idx++) begin : GEN_Block__MiXeD__CASE
            assign out_bus[idx] = in_bus[WIDTH-1-idx];
        end
    endgenerate
endmodule
module path_escape_mod (
    input  logic dummy_in,
    output logic dummy_out
);
    parameter string PATH = "C:\\Program Files\\Verilator\\bin\\verilator.exe";
    assign dummy_out = dummy_in;
endmodule
