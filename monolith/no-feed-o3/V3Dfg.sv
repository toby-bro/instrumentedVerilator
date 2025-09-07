//============================================================
module sel_slice (
    input  logic [31:0] data_in,
    output logic [7:0]  data_out
);
    assign data_out = data_in[23:16];
endmodule
//============================================================
module mux_concat (
    input  logic        sel,
    input  logic [7:0]  in0,
    input  logic [7:0]  in1,
    output logic [7:0]  mux_out
);
    assign mux_out = sel ? in1 : in0;
endmodule
//============================================================
module splice_packed (
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [63:0] splice_out
);
    logic [63:0] temp;
    always_comb begin
        temp[15:0]  = a[15:0];
        temp[31:16] = b[31:16];
        temp[63:32] = 32'hCAFEBABE;
    end
    assign splice_out = temp;
endmodule
//============================================================
module array_manip (
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    logic [7:0] mem [0:3];
    always_comb begin
        mem[0] = in_data;
        mem[1] = mem[0] + 8'd1;
        mem[2] = mem[1] + 8'd1;
        mem[3] = mem[2] + 8'd1;
    end
    assign out_data = mem[3];
endmodule
//============================================================
module const_large (
    input  logic        dummy_in,
    output logic [127:0] const_out
);
    assign const_out = 128'hDEADBEEF0123456789ABCDEF12345678;
endmodule
//============================================================
module arithmetic_ops (
    input  logic [15:0] in_a,
    input  logic [15:0] in_b,
    output logic [15:0] sum,
    output logic [15:0] difference,
    output logic [31:0] product
);
    assign sum        = in_a + in_b;
    assign difference = in_a - in_b;
    assign product    = in_a * in_b;
endmodule
//============================================================
module class_usage (
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    class CExample;
        bit [7:0] id;
        function new();
            id = 8'hA5;
        endfunction
    endclass
    always_comb begin
        CExample obj = new();
        out_val = in_val ^ obj.id;
    end
endmodule
