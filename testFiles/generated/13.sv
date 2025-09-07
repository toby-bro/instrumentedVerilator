module extern_declarations (
    input logic i_in,
    output logic o_out
);
    assign o_out = i_in;
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module simple_undeclared_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_i_bind_control_1755004207265_804,
    input logic inj_i_in_1755004207265_764,
    input logic inj_i_in_1755004207265_970,
    input logic [7:0] inj_in_a_m9_1755004207266_900,
    input logic [7:0] inj_in_b_m9_1755004207266_799,
    input int inj_in_val_1755004207265_448,
    input wire reset,
    output logic inj_data_out_1755004207265_70,
    output logic inj_o_bind_status_1755004207265_997,
    output logic inj_o_out_1755004207265_245,
    output logic inj_o_out_1755004207265_287,
    output logic inj_out_m9_1755004207266_167,
    output int inj_out_val_1755004207265_865,
    output int inj_out_val_1755004207266_478,
    output int inj_out_val_1755004207266_702,
    output logic inj_unused_out_1755004207265_774
);
    // BEGIN: child_scalar_port_ts1755004207265
    // BEGIN: module_to_bind_ts1755004207265
    // BEGIN: unreferenced_module_ts1755004207265
    // BEGIN: definition_used_diag_mod_ts1755004207265
    // BEGIN: attributes_on_expr_port_ts1755004207266
    logic internal_sig_ts1755004207266;
        // BEGIN: unsupported_logand_expr_ts1755004207266
        logic [7:0] var_m9_ts1755004207266;
            simple_undeclared_mod simple_undeclared_mod_inst_1755004207266_4395 (
                .in_val(inj_in_val_1755004207265_448),
                .out_val(inj_out_val_1755004207266_702)
            );
        always_comb begin
            var_m9_ts1755004207266 = inj_in_a_m9_1755004207266_900;
            if ((var_m9_ts1755004207266 > 10) && (inj_in_b_m9_1755004207266_799 < 5)) begin
                inj_out_m9_1755004207266_167 = 1;
            end else begin
                inj_out_m9_1755004207266_167 = 0;
            end
            var_m9_ts1755004207266++;
        end
        // END: unsupported_logand_expr_ts1755004207266

        // BEGIN: invalid_this_diag_mod_ts1755004207266
        assign inj_out_val_1755004207266_478 = inj_in_val_1755004207265_448;
        // END: invalid_this_diag_mod_ts1755004207266

    assign internal_sig_ts1755004207266 = inj_i_in_1755004207265_764 & inj_i_in_1755004207265_970;
    simple_adder sa_inst(
        .a  (inj_i_in_1755004207265_764),
        (* fanout_limit = 10 *) .b(inj_i_in_1755004207265_970),
        .sum(inj_o_out_1755004207265_287)
    );
    // END: attributes_on_expr_port_ts1755004207266

    assign inj_out_val_1755004207265_865 = inj_in_val_1755004207265_448;
    // END: definition_used_diag_mod_ts1755004207265

    assign inj_unused_out_1755004207265_774 = ~inj_i_in_1755004207265_970;
    // END: unreferenced_module_ts1755004207265

    always_comb inj_o_bind_status_1755004207265_997 = |inj_i_bind_control_1755004207265_804;
    // END: module_to_bind_ts1755004207265

    assign inj_data_out_1755004207265_70 = inj_i_in_1755004207265_970;
    // END: child_scalar_port_ts1755004207265

    extern_declarations extern_declarations_inst_1755004207265_9589 (
        .i_in(inj_i_in_1755004207265_970),
        .o_out(inj_o_out_1755004207265_245)
    );
endmodule

