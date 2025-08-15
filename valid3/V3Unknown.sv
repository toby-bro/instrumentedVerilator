module m_bound_sel_read (
    input  logic [3:0] idx,
    output wire        bit_out
);
    wire [7:0] vec = 8'hA5;
    assign bit_out = vec[idx];
endmodule
module m_sel_lhs (
    input  logic [3:0] idx,
    input  logic       data_in,
    output logic [7:0] vec_out
);
    logic [7:0] vec;
    always_comb begin
        vec = 8'h00;
        vec[idx] = data_in;
        vec_out  = vec;
    end
endmodule
module m_x_const (
    input  logic       dummy,
    output wire [4:0]  out
);
    assign out = 5'bx1x1x;
endmodule
module m_wild_cmp (
    input  logic [3:0] a,
    output wire        out
);
    assign out = (a ==? 4'b1x0x);
endmodule
module m_eq_case (
    input  logic [1:0] a,
    output wire        out
);
    assign out = (a === 2'b1x);
endmodule
module m_is_unknown (
    input  logic [3:0] a,
    output wire        out
);
    assign out = $isunknown(a);
endmodule
module m_count_bits (
    input  logic [7:0]  a,
    output wire [31:0] out
);
    assign out = $countbits(a, 1'b1);
endmodule
module m_array_sel_read (
    input  logic [3:0] idx,
    output wire [7:0]  out
);
    logic [7:0] arr [0:15];
    assign out = arr[idx];
endmodule
module m_array_sel_write (
    input  logic [3:0] idx,
    input  logic [7:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] arr [0:15];
    always_comb begin
        arr[idx]  = data_in;
        data_out  = arr[idx];
    end
endmodule
module m_casex (
    input  logic [3:0] sel,
    output logic       out
);
    always_comb begin
        casex (sel)
            4'b1x0x: out = 1'b1;
            4'b0x1x: out = 1'b0;
            default: out = 1'bx;
        endcase
    end
endmodule
