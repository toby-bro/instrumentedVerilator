class MyClass;
endclass
typedef struct packed {
    logic [3:0] a;
    logic [3:0] b;
} mystruct_t;
module mod_concat_slice(
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [7:0] y
);
    assign y = {a, b};
endmodule
module mod_if(
    input  logic [3:0] sel,
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [3:0] y
);
    always @* begin
        if (sel[0])
            y = a;
        else
            y = b;
    end
endmodule
module mod_seq(
    input  logic       clk,
    input  logic       rst,
    input  logic [7:0] d,
    output logic [7:0] q
);
    always @(posedge clk or posedge rst) begin
        if (rst)
            q <= 0;
        else
            q <= d;
    end
endmodule
module mod_mem(
    input  logic       clk,
    input  logic [2:0] addr,
    input  logic [7:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] mem [0:7] = '{8'hAA,8'hBB,8'hCC,8'hDD,8'hEE,8'hFF,8'h11,8'h22};
    always @(posedge clk) begin
        mem[addr]     <= data_in;
        data_out      <= mem[addr];
    end
endmodule
module mod_case(
    input  logic [1:0] sel,
    input  logic [7:0] in0,
    input  logic [7:0] in1,
    input  logic [7:0] in2,
    output logic [7:0] out
);
    always @* begin
        case (sel)
            2'd0: out = in0;
            2'd1: out = in1;
            default: out = in2;
        endcase
    end
endmodule
module mod_for(
    input  logic [7:0] in,
    output logic [7:0] out
);
    integer i;
    always @* begin
        out = 0;
        for (i = 0; i < 8; i = i + 1)
            out = out | (in >> i);
    end
endmodule
module mod_class(
    input  logic clk,
    input  logic en,
    output logic out
);
    MyClass mc;
    always @(posedge clk) begin
        mc  = new();
        out <= en;
    end
endmodule
module mod_struct(
    input  logic in1,
    input  logic in2,
    output logic out1,
    output logic out2
);
    mystruct_t s;
    always @* begin
        s.a         = in1;
        s.b         = in2;
        {out1,out2} = {s.b, s.a};
    end
endmodule
module mod_nested_if(
    input  logic a,
    input  logic b,
    output logic [1:0] out
);
    always @* begin
        if (a) begin
            if (b)
                out = 2'd1;
            else
                out = 2'd2;
        end else
            out = 2'd3;
    end
endmodule
module mod_param #(
    parameter int N = 4
)(
    input  logic [N-1:0] a,
    output logic [N-1:0] b
);
    assign b = ~a;
endmodule
