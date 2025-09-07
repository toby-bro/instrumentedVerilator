module clk_reg (
    input  logic clk,
    input  logic reset,
    input  logic in_data,
    output logic out_data
);
    always_ff @(posedge clk or posedge reset)
        if (reset)
            out_data <= 1'b0;
        else
            out_data <= in_data;
endmodule
module unpack_arr (
    input  logic        clk,
    input  logic [7:0]  in_data,
    output logic [7:0]  out_data
);
    logic [7:0] mem [0:3];                 
    always_ff @(posedge clk) begin
        mem[0] <= in_data;
    end
    assign out_data = mem[0];
endmodule
module multi_width (
    input  logic [63:0] in64,
    input  logic [31:0] in32,
    input  logic [15:0] in16,
    input  logic  [7:0] in8,
    output logic [63:0] out64
);
    logic [63:0] reg64;    
    logic [31:0] reg32;    
    logic [15:0] reg16;    
    logic  [7:0] reg8;     
    always_comb begin
        reg8  = in8;
        reg16 = in16;
        reg32 = in32;
        reg64 = in64 ^ {{32{1'b0}}, reg32};
    end
    assign out64 = reg64;
endmodule
class inc8;
    function logic [7:0] add1 (logic [7:0] v);
        return v + 8'd1;
    endfunction
endclass
module class_user (
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    inc8 c_inst;                       
    always_comb begin
        c_inst = new();                
        out_val = c_inst.add1(in_val);
    end
endmodule
typedef struct packed {
    logic [3:0] a;
    logic [11:0] b;
} packed_s;
module struct_demo (
    input  logic [15:0] in_data,
    output logic [15:0] out_data
);
    packed_s pkt;
    always_comb begin
        pkt.a = in_data[15:12];
        pkt.b = in_data[11:0];
        out_data = {pkt.a, pkt.b};
    end
endmodule
module struct_anon_demo (
    input  logic [15:0] in_data,
    output logic [15:0] out_data
);
    struct packed { logic [3:0] a; logic [11:0] b; } anon_pkt;
    always_comb begin
        anon_pkt.a = in_data[15:12];
        anon_pkt.b = in_data[11:0];
        out_data   = {anon_pkt.a, anon_pkt.b};
    end
endmodule
