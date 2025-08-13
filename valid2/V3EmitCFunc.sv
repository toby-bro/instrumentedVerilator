`default_nettype none
class MyClass;
    rand int value;
    function new();
        value = 0;
    endfunction
    function void set(int v);
        value = v;
    endfunction
    function int get();
        return value;
    endfunction
endclass
module simple_ops #(parameter WIDTH = 16)(
    input  logic [WIDTH-1:0] in_a,
    input  logic [WIDTH-1:0] in_b,
    output logic [WIDTH:0]   out_sum,
    output logic [WIDTH-1:0] out_mix
);
    logic [WIDTH-1:0] tmp;
    assign out_sum = in_a + in_b;
    assign tmp     = (in_a & in_b) | (in_a ^ in_b);
    assign out_mix = (tmp != 0) ? (in_a - in_b) : (in_a >>> 1);
endmodule
module dpi_call(
    input  logic [31:0] d_in,
    output logic [31:0] d_out
);
    import "DPI-C" function int myfunc(input int arg1);
    always_comb begin
        d_out = myfunc(d_in);
    end
endmodule
module wide_const_pack(
    input  logic            ctrl,
    output logic [511:0]    vector_out
);
    localparam [511:0] WIDE_PARAM = 512'h0123456789ABCDEF_FEDCBA9876543210_0011223344556677_8899AABBCCDDEEFF_0123456789ABCDEF_FEDCBA9876543210_0011223344556677_8899AABBCCDDEEFF;
    assign vector_out = ctrl ? WIDE_PARAM : ~WIDE_PARAM;
endmodule
module pack_conv(
    input  logic [511:0] vect_in,
    output logic [511:0] vect_out
);
    logic [7:0] byte_array [0:63];
    always_comb begin
        {<<8{byte_array}} = vect_in;
        vect_out = {<<8{byte_array}};
    end
endmodule
module str_conv(
    input  logic  [7:0]   dummy_in,
    output logic [95:0]  str_bits_out
);
    localparam string HELLO_STR = "HelloWorld!";
    localparam logic [95:0] HELLO_BITS = "HelloWorld!";
    assign str_bits_out = HELLO_BITS ^ {12{dummy_in}};
endmodule
module class_test(
    input  logic        clk,
    input  logic        rst_n,
    input  logic [31:0] in_data,
    output logic [31:0] out_data
);
    MyClass ch;
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            ch = new();
            out_data <= 0;
        end else begin
            if (ch == null) ch = new();
            ch.set(in_data);
            out_data <= ch.get();
        end
    end
endmodule
module array_test(
    input  logic        clk,
    input  logic [7:0]  idx,
    output logic [31:0] value_out
);
    int dyn_array[];
    int queue_data[$];
    int assoc_array[string];
    string s_key;
    always_ff @(posedge clk) begin
        if (dyn_array.size() == 0) begin
            dyn_array = new[4];
            dyn_array[0] = 1;
            dyn_array[1] = 2;
            dyn_array[2] = 3;
            dyn_array[3] = 4;
        end
        queue_data.push_back(idx);
        s_key = "key";
        assoc_array[s_key] = 10;
        value_out <= dyn_array[idx & 3] + queue_data.size() + assoc_array[s_key];
    end
endmodule
`default_nettype wire
