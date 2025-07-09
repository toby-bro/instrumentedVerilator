module inside_expr_mod(
    input  logic [3:0] in_val,
    output logic       match
);
    always_comb begin
        match = in_val inside { [4'h0:4'h8], 4'hF };
    end
endmodule
module assignment_pattern_mod(
    input  logic [3:0] sel,
    output logic [31:0] out_bus
);
    typedef struct packed {
        logic [7:0] a, b, c, d;
    } t_s;
    t_s s;
    always_comb begin
        s = '{default:8'h00, a:8'hAA, c:8'h55};
        out_bus = {s.a, s.b, s.c, s.d} << sel;
    end
endmodule
module stream_concat_mod(
    input  logic [31:0] data_in,
    output logic [31:0] data_out
);
    always_comb begin
        data_out = {>>{data_in}};
    end
endmodule
module multiple_concat_mod(
    input  logic [7:0]  byte_in,
    output logic [31:0] word_out
);
    always_comb begin
        word_out = {4{byte_in}};
    end
endmodule
module element_select_mod(
    input  logic [31:0] word_in,
    output logic [7:0]  high_byte
);
    always_comb begin
        high_byte = word_in[31:24];
    end
endmodule
module postfix_inc_mod(
    input  logic clk,
    input  logic rst,
    output logic [3:0] count
);
    always_ff @(posedge clk or posedge rst) begin
        if (rst) count <= '0;
        else     count++;
    end
endmodule
module cast_expr_mod(
    input  logic signed [7:0] signed_in,
    output logic        [7:0] unsigned_out
);
    always_comb begin
        unsigned_out = unsigned'(signed_in);
    end
endmodule
module new_expr_mod(
    input  logic [3:0] in_val,
    output logic [3:0] out_val
);
    class myc;
        logic [3:0] v;
        function new(logic [3:0] iv); v = iv; endfunction
    endclass
    myc handle;
    always_comb begin
        handle = new(in_val);
        out_val = handle.v;
    end
endmodule
module array_with_method_mod(
    input  logic        clk,
    input  logic        start,
    input  logic [3:0]  factor,
    output int          result
);
    int arr [0:3] = '{1, 2, 3, 4};
    class rand_c;
        rand logic [7:0] val;
        constraint c { val inside {[8'h10:8'hF0]}; }
    endclass
    rand_c h;
    always_ff @(posedge clk) begin
        if (h == null) h = new();
        if (start) void'(h.randomize() with { val[0] == 1'b0; });
    end
    always_comb begin
        result = arr.sum with (int'(item * factor));
    end
endmodule
module event_expr_mod(
    input  logic clk,
    input  logic rst_n,
    input  logic din,
    output logic dout
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) dout <= 1'b0;
        else        dout <= din;
    end
endmodule
module seq_prop_mod(
    input  logic clk,
    input  logic req,
    input  logic gnt,
    output logic dummy
);
    sequence s1;
        req ##1 gnt;
    endsequence
    property p1;
        @(posedge clk) s1 |-> gnt;
    endproperty
    assert property (p1);
    assign dummy = gnt;
endmodule
module min_typ_max_mod(
    input  logic dummy_in,
    output int   out_val
);
    localparam int P = (1:2:3);
    assign out_val = P + dummy_in;
endmodule
module cond_expr_mod(
    input  logic a,
    input  logic b,
    input  logic c,
    output logic result
);
    assign result = a ? b : c;
endmodule
