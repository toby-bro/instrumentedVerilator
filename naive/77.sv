interface simple_if(input logic clk, input logic rst);
    logic sig;
    modport slave (input sig, clk, rst);
endinterface
module param_mod #(parameter WIDTH = 8) (input logic [WIDTH-1:0] in, output logic [WIDTH*2-1:0] out);
    assign out = {in, in};
endmodule
module struct_mod(input logic [7:0] data_in, output logic [7:0] data_out);
    typedef struct packed { logic [3:0] lo; logic [3:0] hi; } nibble_t;
    nibble_t s_in, s_out;
    assign s_in = '{lo: data_in[3:0], hi: data_in[7:4]};
    assign s_out = '{lo: s_in.hi, hi: s_in.lo};
    assign data_out = {s_out.hi, s_out.lo};
endmodule
module enum_mod(input logic [1:0] sel, output logic out);
    typedef enum logic [1:0] {IDLE = 2'b00, BUSY = 2'b01, DONE = 2'b10} state_t;
    state_t state;
    always_comb begin
        state = state_t'(sel);
        out = (state == DONE);
    end
endmodule
module gen_if_mod #(parameter FLAG = 1) (input logic in, output logic out);
    generate
        if (FLAG) begin
            assign out = in;
        end else begin
            assign out = ~in;
        end
    endgenerate
endmodule
module gen_for_mod #(parameter N = 4) (input logic en, output logic [N-1:0] bits);
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : gen_loop
            assign bits[i] = en & (i % 2);
        end
    endgenerate
endmodule
module always_ff_mod(input logic clk, rst, d, output logic q);
    always_ff @(posedge clk) begin
        if (rst)
            q <= 0;
        else
            q <= d;
    end
endmodule
module always_latch_mod(input logic en, in, output logic out);
    always_latch begin
        if (en)
            out = in;
    end
endmodule
module function_mod(input logic [7:0] a, b, output logic [7:0] c);
    function logic [7:0] add(logic [7:0] x, logic [7:0] y);
        add = x + y;
    endfunction
    assign c = add(a, b);
endmodule
class my_reg;
    logic q;
    function void write(logic d);
        q = d;
    endfunction
    function logic read();
        return q;
    endfunction
endclass
module class_mod(input logic clk, input logic din, output logic out);
    my_reg reg_inst;
    always_ff @(posedge clk) begin
        reg_inst = new();
        reg_inst.write(din);
        out <= reg_inst.read();
    end
endmodule
module cover_assert_mod(input logic clk, in, output logic out);
    logic [3:0] cnt;
    always_ff @(posedge clk) begin
        cnt <= cnt + in;
        out <= cnt[3];
    end
    property p_in_implies_out;
        @(posedge clk) in |-> ##1 out;
    endproperty
    assert property (p_in_implies_out);
    cover property (p_in_implies_out);
endmodule
module interface_mod(input logic clk, input logic rst, output logic out);
    simple_if if_inst(.clk(clk), .rst(rst));
    always_ff @(posedge if_inst.clk) begin
        if (if_inst.rst)
            out <= 0;
        else
            out <= if_inst.sig;
    end
endmodule
