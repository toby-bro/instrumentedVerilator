virtual class base_vc;
  pure virtual function int compute(int a);
endclass
class derived_c extends base_vc;
  function int compute(int a);
    compute = a + 1;
  endfunction
endclass
class rand_holder;
  rand bit [7:0] v;
  constraint c_v { v inside {[8'd0:8'd100]}; }
endclass
module cast_assign #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in_sig,
    output logic             out_gt
);
    assign out_gt = int'(in_sig) > 0;
endmodule
module param_type_nbassign #(parameter type T = logic [3:0]) (
    input  logic clk,
    input  T     din,
    output T     dout
);
    T tmp;
    always_ff @(posedge clk) begin
        tmp <= din;
    end
    assign dout = tmp;
endmodule
module struct_union (
    input  logic [3:0] sel,
    output logic [7:0] y
);
    typedef enum logic [1:0] {S0 = 2'b00, S1 = 2'b01, S2 = 2'b10} state_t;
    typedef struct packed {
        logic [3:0] a;
        logic [3:0] b;
    } my_struct_t;
    typedef union packed {
        logic [7:0] byte_val;
        struct packed {
            logic [3:0] low;
            logic [3:0] high;
        } nibbles;
    } my_union_t;
    my_struct_t s;
    my_union_t  u;
    always_comb begin
        s.a = sel;
        s.b = ~sel;
        u.byte_val = {s.a, s.b};
    end
    assign y = u.byte_val;
endmodule
module class_use (
    input  logic [31:0] in_val,
    output logic [31:0] out_val
);
    derived_c d;
    always_comb begin
        if (d == null) begin
            d = new;
        end
        out_val = d.compute(int'(in_val));
    end
endmodule
module constraint_module (
    input  logic        clk,
    output logic [7:0]  rnd_out
);
    rand_holder rh;
    always_ff @(posedge clk) begin
        if (rh == null) rh = new;
        void'(rh.randomize());
        rnd_out <= rh.v;
    end
endmodule
module func_module (
    input  logic [15:0] in_data,
    output logic [15:0] out_data
);
    function automatic logic [15:0] swap_bytes (input logic [15:0] d);
        swap_bytes = {d[7:0], d[15:8]};
    endfunction
    assign out_data = swap_bytes(in_data);
endmodule
