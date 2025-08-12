module mod_arith(
    input  logic [7:0] i_a,
    input  logic [7:0] i_b,
    output logic [7:0] o_sum
);
    assign o_sum = i_a + i_b;
endmodule
module mod_sequential(
    input  logic        clk,
    input  logic        rst,
    input  logic [3:0]  i_d,
    output logic [3:0]  o_q
);
    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            o_q <= '0;
        else
            o_q <= i_d;
    end
endmodule
module mod_conditional #(
    parameter int WIDTH = 8
)(
    input  logic [WIDTH-1:0] i_data,
    output logic [WIDTH-1:0] o_data
);
    generate
        if (WIDTH > 4)
            assign o_data = i_data << 1;
        else
            assign o_data = i_data >> 1;
    endgenerate
endmodule
module mod_generate_loop #(
    parameter int N = 4
)(
    input  logic [N-1:0] i_vec,
    output logic [N-1:0] o_rev
);
    genvar idx;
    generate
        for (idx = 0; idx < N; idx = idx + 1) begin
            assign o_rev[idx] = i_vec[N-1-idx];
        end
    endgenerate
endmodule
module mod_function(
    input  logic [15:0] i_val,
    output logic [7:0]  o_byte
);
    function automatic logic [7:0] get_low_byte(input logic [15:0] val);
        get_low_byte = val[7:0];
    endfunction
    always_comb begin
        o_byte = get_low_byte(i_val);
    end
endmodule
module mod_task(
    input  logic [3:0] i_val,
    output logic [3:0] o_out
);
    task automatic compute(input logic [3:0] in, output logic [3:0] out);
        begin
            out = (in * 3) ^ 4'hA;
        end
    endtask
    always_comb begin
        compute(i_val, o_out);
    end
endmodule
module mod_enum(
    input  logic [1:0] sel,
    input  logic [3:0] i_a,
    input  logic [3:0] i_b,
    output logic [3:0] o_f
);
    typedef enum logic [1:0] {
        ADD    = 2'b00,
        SUB    = 2'b01,
        AND_OP = 2'b10,
        OR_OP  = 2'b11
    } op_e;
    logic [3:0] res;
    always_comb begin
        case (sel)
            ADD:    res = i_a + i_b;
            SUB:    res = i_a - i_b;
            AND_OP: res = i_a & i_b;
            default:res = i_a | i_b;
        endcase
    end
    always_comb begin
        o_f = res;
    end
endmodule
module mod_class(
    input  logic        clk,
    input  logic        rst,
    input  logic [7:0]  i_a,
    input  logic [7:0]  i_b,
    output logic [7:0]  o_sum
);
    class adder;
        rand logic [7:0] x;
        rand logic [7:0] y;
        function logic [7:0] sum();
            sum = x + y;
        endfunction
    endclass
    adder inst;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            inst = new();
            inst.x = 0;
            inst.y = 0;
            o_sum <= 0;
        end else begin
            inst.x = i_a;
            inst.y = i_b;
            o_sum <= inst.sum();
        end
    end
endmodule
module mod_struct(
    input  logic [3:0] i_in,
    output logic [1:0] o_out
);
    typedef struct packed {
        logic     a;
        logic [1:0] b;
        logic     c;
    } my_s;
    my_s s;
    always_comb begin
        s.a = i_in[0];
        s.b = i_in[2:1];
        s.c = i_in[3];
        o_out = {s.a, s.c};
    end
endmodule
module mod_latch(
    input  logic       en,
    input  logic [3:0] i_d,
    output logic [3:0] o_q
);
    always_latch begin
        if (en)
            o_q = i_d;
    end
endmodule
