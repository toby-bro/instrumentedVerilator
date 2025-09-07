module simple_ops_mod(input  logic [7:0] a,
                      input  logic [7:0] b,
                      input  logic [7:0] c,
                      output logic [7:0] y);
    assign y = (a + b) ^ (~c);
endmodule
module wide_const_mod(input  logic dummy_in,
                      output logic [511:0] wide_out);
    assign wide_out = 512'h0123456789ABCDEF_FEDCBA9876543210_0011223344556677_8899AABBCCDDEEFF_0123456789ABCDEF_FEDCBA9876543210_0011223344556677_8899AABBCCDDEEFF;
endmodule
module dpi_caller_mod(input  logic [31:0] x,
                      output logic [31:0] y);
    import "DPI-C" function int my_cfunc(input int a, input int b);
    always_comb begin
        y = my_cfunc(x, 32'hDEADBEEF);
    end
endmodule
module class_mod(input  logic trig,
                 output logic [31:0] out);
    class sample;
        int data;
        function new(int d); data = d; endfunction
        function int get(); return data; endfunction
    endclass
    sample obj;
    always_comb begin
        obj = new(100);
        out = obj.get();
    end
endmodule
module wide_array_mod(input  logic [31:0] in0,
                      output logic [127:0] out_wide);
    bit [31:0] arr[4];
    always_comb begin
        arr[0] = in0;
        arr[1] = in0 + 1;
        arr[2] = in0 + 2;
        arr[3] = in0 + 3;
        out_wide = {arr[3], arr[2], arr[1], arr[0]};
    end
endmodule
module assoc_array_mod(input  logic [15:0] sel,
                       output logic [31:0] value);
    int aa[int];
    int i_sel;
    always_comb begin
        aa[0] = 123;
        aa[1] = 456;
        i_sel = sel;
        if (aa.exists(i_sel))
            value = aa[i_sel];
        else
            value = 0;
    end
endmodule
module sformat_mod(input  logic [31:0] val,
                   output logic [95:0] packed_out);
    bit [95:0] const_pack = 96'h564552494C41544F525F;
    string formatted;
    always_comb begin
        formatted  = $sformatf("Value=%0d", val);
        packed_out = const_pack;
    end
endmodule
