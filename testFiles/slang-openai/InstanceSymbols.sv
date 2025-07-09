interface simple_if (input logic clk);
    logic data;
endinterface
checker signal_stable (input logic sig);
    default clocking @(posedge sig); endclocking
endchecker
module param_mod #(parameter WIDTH = 1)
                  (input  logic [WIDTH-1:0] a,
                   output logic [WIDTH-1:0] y);
    assign y = ~a;
endmodule
module inst_array_mod #(parameter WIDTH = 1)
                       (input  logic a_in,
                        output wire y_out);
    param_mod #(.WIDTH(1)) u [0:1][0:3] (.a(a_in), .y(y_out));
endmodule
module prim_mod (input logic a,
                 input logic b,
                 output logic y);
    wire yw;
    and and_gate (yw, a, b);
    assign y = yw;
endmodule
module gen_uninst_mod (input logic in_sig,
                       output logic out_sig);
    localparam int USE = 0;
    generate
        if (USE) begin : blk
            undef_mod u0();
        end
    endgenerate
    assign out_sig = in_sig;
endmodule
module checker_mod (input logic clk,
                    output logic y);
    signal_stable chk0 (.sig(clk));
    assign y = clk;
endmodule
module iface_user (simple_if intf,
                   input  logic din,
                   output logic dout);
    assign intf.data = din;
    assign dout      = intf.data;
endmodule
module iface_root (simple_if intf,
                   input  logic din,
                   output logic dout);
    assign intf.data = din;
    assign dout      = intf.data;
endmodule
module typeparam_mod #(type T = int)
                      (input  T in_val,
                       output T out_val);
    assign out_val = in_val;
endmodule
module bound_mon (input logic a,
                  output logic dummy);
    assign dummy = a;
endmodule
bind param_mod bound_mon bm_inst (.a(a));
module iface_wrapper (input logic din,
                      output logic dout);
    simple_if intf1(din);
    simple_if intf2(din);
    wire dout_root;
    iface_user iu (intf1, din, dout);
    iface_root ir (intf2, din, dout_root);
endmodule
