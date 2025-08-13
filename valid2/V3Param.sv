module param_mod #(
    parameter int    P = 4,
    parameter real   R = 2.0,
    parameter string S = "DEF"
) (
    input  logic [P-1:0] in,
    output logic [P-1:0] out
);
    assign out = in;
endmodule
module use_param_mod #(
    parameter int WIDTH = 8
) (
    input  logic [WIDTH-1:0]  din,
    output logic [WIDTH-1:0]  dout
);
    param_mod #(.P(WIDTH), .R(3.1415), .S("HELLO")) u_param (
        .in (din),
        .out(dout)
    );
endmodule
module type_param_mod #(
    parameter type T = logic
) (
    input  T in,
    output T out
);
    assign out = in;
endmodule
module use_type_param_mod (
    input  logic [7:0] din,
    output logic [7:0] dout
);
    type_param_mod #(.T(logic [7:0])) u_type (
        .in (din),
        .out(dout)
    );
endmodule
module gen_mod #(
    parameter int N = 4
) (
    input  logic [N-1:0] din,
    output logic [N-1:0] dout
);
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : g
            assign dout[i] = din[i];
        end
    endgenerate
endmodule
module gen_case_mod #(
    parameter int SEL = 0
) (
    input  logic  din,
    output logic  dout
);
    generate
        if (SEL == 0) begin
            assign dout = din;
        end else begin
            case (SEL)
                1:  assign dout = ~din;
                default: assign dout = 1'b0;
            endcase
        end
    endgenerate
endmodule
interface my_ifc #(
    parameter int W = 8
);
    logic [W-1:0] data;
    modport host (input data);
endinterface
module intf_consumer #(
    parameter int W = 8
) (
    my_ifc.host ifc,
    output logic [W-1:0] out
);
    assign out = ifc.data;
endmodule
module intf_wrapper (
    input  logic [7:0] din,
    output logic [7:0] dout
);
    my_ifc #(.W(8)) if_inst();
    assign if_inst.data = din;
    intf_consumer #(.W(8)) u_cons (
        .ifc(if_inst),
        .out(dout)
    );
endmodule
class cparam #(int N = 4);
    int data [N];
    function void dummy(); endfunction
endclass
module class_user (
    input  logic in_sig,
    output logic out_sig
);
    always_comb begin
        cparam #(8) obj = new();
        out_sig = in_sig;
    end
endmodule
