module recursive_param_diag_mod (
    input int dummy_in,
    output int out_val
);
    assign out_val = dummy_in;
endmodule

module child_iface_port (
    input wire clk,
    input logic iface_child_input,
    input int inj_dummy_in_1755538448203_389,
    input wire rst,
    output logic iface_child_output,
    output int inj_out_val_1755538448203_777
);
    recursive_param_diag_mod recursive_param_diag_mod_inst_1755538448203_8955 (
        .dummy_in(inj_dummy_in_1755538448203_389),
        .out_val(inj_out_val_1755538448203_777)
    );
    assign if_inst.signal_b = ~if_inst.signal_a;
    assign iface_child_output = iface_child_input;
endmodule

