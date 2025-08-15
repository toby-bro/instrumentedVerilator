interface simple_if (input bit clk);
    logic data;
    modport m (input clk, input data);
endinterface
class base_c;
    virtual function int foo();
        foo = 0;
    endfunction
endclass
class derived_c extends base_c;
    int val;
    function new(int v = 0);
        val = v;
    endfunction
    virtual function int foo();
        return val;
    endfunction
endclass
class rand_c;
    rand bit [7:0] a;
    constraint c1 { a inside { [8'h10 : 8'h20] }; }
endclass
module enum_mod #(parameter string PSTR = "text",
                  parameter real   PREAL = 3.14)
                 (input  logic [3:0] ctrl,
                  output logic       flag);
    typedef enum logic [1:0] { S0 = 2'd0, S1 = 2'd1, S2 = 2'd2 } state_e;
    state_e state;
    always_comb begin
        unique0 case (ctrl[1:0])
            2'd0: state = S0;
            2'd1: state = S1;
            default: state = S2;
        endcase
        flag = (state == S1);
    end
endmodule
module struct_array_mod (input  logic       clk,
                         input  logic       rst,
                         output logic [7:0] sum);
    typedef struct packed {
        logic [3:0] a;
        logic [3:0] b;
    } pair_t;
    pair_t arr [0:3];
    pair_t tmp;
    always_ff @(posedge clk) begin
        if (rst) begin
            arr[0].a <= 4'h0;
            arr[0].b <= 4'h0;
        end
        tmp <= arr[0];
    end
    assign sum = tmp.a + tmp.b;
endmodule
module complex_array_mod (input  logic sel,
                          output logic is_nonempty);
    int dyn[];
    int aa[string];
    int q[$];
    always_comb is_nonempty = (q.size() != 0);
endmodule
module clocking_mod (input  logic clk,
                     output logic dummy);
    clocking cb @(posedge clk);
    endclocking
    event ev;
    assign dummy = 1'b0;
endmodule
module vif_mod (input  logic        sel,
                simple_if.m         vif,
                output logic        out_data);
    assign out_data = sel & vif.data;
endmodule
module class_mod (input  logic [7:0] in_val,
                  output logic [7:0] out_val);
    function automatic int compute(input int v);
        derived_c dc = new(v);
        return dc.foo();
    endfunction
    rand_c rc;
    assign out_val = compute(in_val);
endmodule
module inside_mod (input  logic [3:0] data,
                   output logic       match);
    assign match = (data inside { [4'h0 : 4'h7] });
endmodule
module eq_mod (input  logic [3:0] a,
               input  logic [3:0] b,
               output logic       res);
    assign res = (a === b);
endmodule
module typedef_mod (input  logic sel,
                    output logic y);
    typedef logic [3:0] my_t;
    typedef my_t another_t;
    another_t a = 4'b0011;
    assign y = sel ? a[0] : a[1];
endmodule
module wiretype_mod (input  logic in_sig,
                     output logic out_sig);
    tri pwire;
    assign pwire   = in_sig;
    assign out_sig = pwire;
endmodule
module assert_mod (input  logic       clk,
                   input  logic       rst,
                   input  logic [7:0] d,
                   output logic       ok);
    property p1;
        @(posedge clk) disable iff (rst) d inside { [8'h00 : 8'hFF] };
    endproperty
    assert property (p1);
    assign ok = 1'b1;
endmodule
