module mod_param #(parameter WIDTH = 8, parameter signed OFFSET = 1) (
    input  logic [WIDTH-1:0] in,
    output logic signed [WIDTH-1:0] out
);
    localparam signed DOUBLE_OFFSET = OFFSET * 2;
    assign out = in + DOUBLE_OFFSET;
endmodule
module mod_struct_enum (
    input  logic           enable,
    input  logic [1:0]     sel,
    output logic [7:0]     data
);
    typedef enum logic [1:0] { A = 2'b00, B = 2'b01, C = 2'b10 } enum_t;
    typedef struct packed { logic [3:0] high; logic [3:0] low; } struct_t;
    enum_t    state;
    struct_t  reg_data;
    always_comb begin
        case (sel)
            A: begin state = A; reg_data = '{high:4'hA, low:4'h5}; end
            B: begin state = B; reg_data = '{high:4'hB, low:4'h6}; end
            default: begin state = C; reg_data = '{high:4'hF, low:4'h0}; end
        endcase
        data = enable ? {reg_data.high, reg_data.low} : 8'h00;
    end
endmodule
module mod_memory (
    input  logic        clk,
    input  logic        we,
    input  logic        re,
    input  logic [3:0]  addr,
    input  logic [7:0]  din,
    output logic [7:0]  dout
);
    logic [7:0] mem [0:15];
    always_ff @(posedge clk) if (we) mem[addr] <= din;
    assign dout = re ? mem[addr] : 8'hXX;
endmodule
module mod_generate (
    input  logic [3:0] in,
    input  logic       en,
    output logic [3:0] out
);
    genvar i;
    logic [3:0] tmp;
    generate
        for (i = 0; i < 4; i = i + 1) begin : genblk
            assign tmp[i] = in[i] & en;
        end
    endgenerate
    assign out = tmp;
endmodule
module mod_function (
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic       sel,
    output logic [7:0] y
);
    function logic [7:0] mux(input logic [7:0] x, y, input logic s);
        return s ? y : x;
    endfunction
    assign y = mux(a, b, sel);
endmodule
module mod_ff (
    input  logic        clk,
    input  logic        rst,
    input  logic [7:0]  in,
    output logic [7:0]  out
);
    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            out <= '0;
        else
            out <= in;
    end
endmodule
module mod_comb (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [3:0] sum,
    output logic       carry
);
    always_comb begin
        {carry, sum} = a + b;
    end
endmodule
module mod_class (
    input  logic        clk,
    input  logic        in,
    output logic        out
);
    logic res;
    class MyClass;
        function logic compute(logic a);
            return !a;
        endfunction
    endclass
    MyClass obj;
    always_ff @(posedge clk) begin
        obj = new();
        res = obj.compute(in);
    end
    assign out = res;
endmodule
module mod_typedef (
    input  logic [7:0] in,
    output logic [7:0] out
);
    typedef logic [7:0] byte_t;
    localparam byte_t CONST = 8'hFF;
    assign out = in ^ CONST;
endmodule
