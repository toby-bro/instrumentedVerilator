module supply_and_real_mod(
    input  logic [3:0] in_sig,
    output logic       out_sig
);
    supply1 VDD;
    supply0 VSS;
    real analog_bus;
    assign out_sig = in_sig[0];
endmodule
module array_types_mod(
    input  logic [7:0] in_bus,
    output logic [15:0] out_bus
);
    logic [3:0] packed_vec;
    logic [7:0] unpacked_arr [0:3];
    logic [1:0] multi_dim [0:1] [0:2];
    int dyn_arr[];
    int q_arr[$];
    int q_arr2[$:3];
    int assoc_str [string];
    int assoc_wild [*];
    assign out_bus = {in_bus, packed_vec};
endmodule
module attribute_function_mod(
    input  logic [3:0] data_in,
    output logic [3:0] data_out
);
    (* myAttr = "hello_world" *) logic [3:0] attr_sig;
    function automatic logic [3:0] combiner(input logic [3:0] a, input logic [3:0] b);
        combiner = a ^ b;
    endfunction
    assign attr_sig = combiner(data_in, data_in);
    assign data_out = attr_sig;
endmodule
module property_example_mod(
    input  logic clk,
    input  logic a,
    input  logic b,
    output logic y
);
    property p_typed(bit x, bit y_sig);
        @(posedge clk) x |-> y_sig;
    endproperty
    property p_untyped;
        @(posedge clk) a |-> b;
    endproperty
    assign y = a & b;
endmodule
