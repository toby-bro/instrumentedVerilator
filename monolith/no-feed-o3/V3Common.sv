typedef struct {
    logic [3:0]   a;
    int           b;
    logic [127:0] c;
} my_struct_t;
typedef union {
    logic [7:0] s;
    int         t;
} my_union_t;
interface simple_if;
    logic req;
    modport master (input  req);
    modport slave  (output req);
endinterface
class base_c;
    int id;
    rand int random_value;
    function void incr(input int delta);
        id += delta;
    endfunction
endclass
class derived_c extends base_c;
    logic [15:0]   extra;
    bit   [127:0]  wide_var;
endclass
module m_wide (
    input  logic [127:0] in_data,
    output logic [127:0] out_data
);
    assign out_data = in_data;
endmodule
module m_struct (
    input  logic       sel,
    output logic [31:0] out_val
);
    my_struct_t s;
    always_comb begin
        s.a = 4'hA;
        s.b = 32'd5;
        s.c = 128'h1;
        if (sel)
            out_val = s.b;
        else
            out_val = 32'd0;
    end
endmodule
module m_union (
    input  logic [7:0] in_b,
    output logic [7:0] out_b
);
    my_union_t u;
    always_comb begin
        u.s = in_b;
        out_b = u.s;
    end
endmodule
module m_class (
    input  logic clk,
    input  logic reset_n,
    output logic flag
);
    always_ff @(posedge clk) begin
        if (!reset_n) begin
            flag <= 1'b0;
        end else begin
            derived_c obj = new();
            obj.incr(1);
            flag <= ~flag;
        end
    end
endmodule
module m_ifc (
    simple_if.slave s_port,
    input  logic    enable,
    output logic    done
);
    assign s_port.req = enable;
    assign done       = s_port.req;
endmodule
