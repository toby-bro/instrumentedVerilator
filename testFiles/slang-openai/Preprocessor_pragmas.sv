module pragma_protect_basic (
    input  logic in_sig,
    output logic out_sig
);
    assign out_sig = in_sig;
endmodule
module pragma_protected_section (
    input  logic din,
    output logic dout
);
    assign dout = din;
endmodule
module pragma_protect_encoding_example (
    input  logic [7:0] data_in,
    output logic [7:0] data_out
);
    assign data_out = data_in;
endmodule
module pragma_protect_key_block_example (
    input  logic clk,
    output logic clk_out
);
    `define MACRO_TOKEN 8'hA5
    logic [7:0] tmp = `MACRO_TOKEN;
    assign clk_out = clk & tmp[0];
endmodule
module pragma_protect_license_example (
    input  logic sig_i,
    output logic sig_o
);
    assign sig_o = sig_i;
endmodule
module pragma_protect_viewport_example (
    input  logic a_in,
    output logic a_out
);
    assign a_out = a_in;
endmodule
module pragma_protect_reset_example (
    input  logic rst_in,
    output logic rst_out
);
    assign rst_out = rst_in;
endmodule
module pragma_resetall_once_example (
    input  logic i_sig,
    output logic o_sig
);
    assign o_sig = i_sig;
endmodule
module pragma_diagnostic_example (
    input  logic d_in,
    output logic d_out
);
    assign d_out = d_in;
endmodule
module pragma_single_arg_ignore_example (
    input  logic s_in,
    output logic s_out
);
    assign s_out = s_in;
endmodule
