module param_demo #(parameter int WIDTH = 8) (
    input  logic [WIDTH-1:0] in_data,
    output logic [WIDTH-1:0] out_data
);
    assign out_data = in_data;
endmodule
module enum_struct_demo (
    input  logic [1:0] sel,
    output logic [3:0] result
);
    typedef enum logic [1:0] {
        ZERO   = 2'b00,
        ONE    = 2'b01,
        TWO    = 2'b10,
        THREE  = 2'b11
    } my_enum_t;
    typedef struct packed {
        logic [3:0] val;
    } my_struct_t;
    my_enum_t    e;
    my_struct_t  s;
    always_comb begin
        e = my_enum_t'(sel);
        case (e)
            ZERO  : s.val = 4'd0;
            ONE   : s.val = 4'd1;
            TWO   : s.val = 4'd2;
            THREE : s.val = 4'd3;
        endcase
        result = s.val;
    end
endmodule
module generate_demo #(parameter int N = 4) (
    input  logic [N-1:0] in_vec,
    output logic [N-1:0] out_vec
);
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_blk
            wire w;
            assign w       = in_vec[i];
            assign out_vec[i] = w;
        end
    endgenerate
endmodule
module primitive_demo (
    input  logic a,
    input  logic b,
    output logic y
);
    wire w;
    and and_gate  (w, a, b);   
    buf buf_gate  (y, w);
endmodule
module dpi_demo (
    input  logic clk,
    output logic done
);
    import "DPI-C" function int c_add (input int a, input int b);
    int result;
    always_ff @(posedge clk) begin
        result <= c_add(1, 2);
        done   <= (result == 3);
    end
endmodule
module class_demo (
    input  logic clk,
    output logic [7:0] count
);
    class Counter;
        int c;
        function new(); c = 0; endfunction
        function void inc(); c++; endfunction
        function int value(); return c; endfunction
    endclass
    Counter ctr;
    always_ff @(posedge clk) begin
        if (ctr == null)
            ctr = new();
        ctr.inc();
        count <= ctr.value()[7:0];
    end
endmodule
module nettype_demo (
    input  logic in_sig,
    output logic out_sig
);
    tri tri_node;
    assign tri_node = in_sig;
    assign out_sig  = tri_node;
endmodule
