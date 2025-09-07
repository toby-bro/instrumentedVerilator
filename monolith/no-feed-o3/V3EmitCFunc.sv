module arith_simple_mod (
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] y
);
    assign y = a + b;
endmodule
module wide_const_mod #(
    parameter logic [255:0] CONST_WIDE = 256'h0123_4567_89AB_CDEF_FEDC_BA98_7654_3210_FFFF_0000_1111_2222
) (
    input  logic        sel,
    output logic [255:0] out_val
);
    assign out_val = CONST_WIDE ^ {256{sel}};
endmodule
module sformatf_mod (
    input  logic [7:0]  byte_in,
    output string       formatted
);
    always_comb begin
        formatted = $sformatf("Byte:%02h", byte_in);
    end
endmodule
module pack_str_mod (
    input  string            s_in,
    output logic [127:0]      packed
);
    always_comb begin
        packed = s_in;          
    end
endmodule
module cvt_wide_array_mod (
    input  logic [127:0]      wide_in,
    output logic [31:0]       array_out [0:3]
);
    always_comb begin
        for (int i = 0; i < 4; i++) begin
            array_out[i] = wide_in[i*32 +: 32];
        end
    end
endmodule
module array_mod (
    input  logic        clk,
    input  logic [7:0]  idx,
    output logic [31:0] data_out
);
    int unsigned dyn_array[];
    int unsigned queue_int[$];
    int unsigned assoc_int[int];
    always_ff @(posedge clk) begin
        if (dyn_array.size() == 0) begin
            dyn_array = new[4];
            for (int i = 0; i < 4; i++) dyn_array[i] = i;
        end
        if (queue_int.size() == 0) begin
            foreach (dyn_array[i]) queue_int.push_back(dyn_array[i]);
        end
        assoc_int[0] = 32'hDEAD_BEEF;
        assoc_int[1] = 32'hCAFE_BABE;
    end
    always_comb begin
        if (idx < dyn_array.size())
            data_out = dyn_array[idx];
        else
            data_out = assoc_int[int'(idx)];
    end
endmodule
module dpi_call_mod (
    input  int in_a,
    input  int in_b,
    output int out_c
);
    import "DPI-C" function int sv_c_add (input int a, input int b);
    always_comb begin
        out_c = sv_c_add(in_a, in_b);
    end
endmodule
module class_mod (
    input  int in_a,
    input  int in_b,
    output int out_mult
);
    class mul_class;
        function int mult (int x, int y);
            mult = x * y;
        endfunction
    endclass
    mul_class mc;
    always_comb begin
        mc = new();
        out_mult = mc.mult(in_a, in_b);
    end
endmodule
