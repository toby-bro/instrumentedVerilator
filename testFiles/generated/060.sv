module SimpleLoopExample (
    input logic [7:0] in_vec,
    output logic [7:0] out_vec
);
    always_comb begin
        for (int i = 0; i < 8; i++) begin
            out_vec[i] = in_vec[7 - i];
        end
    end
endmodule

module module_with_param (
    input logic in,
    output logic named_out
);
    parameter int DELAY = 10;
    logic bind_dummy_in;
    logic bind_dummy_out;
    assign named_out = in;
endmodule

module snippet (
    input wire clk,
    input bit inj_enable_in_1755007771723_203,
    input logic inj_in_1755007771723_163,
    input int inj_in_port_1755007771723_429,
    input logic [7:0] inj_in_vec_1755007771722_751,
    input logic [7:0] inj_sub_val_m2_1755007771723_800,
    input logic [31:0] inj_wide_data_in_1755007771723_555,
    input wire reset,
    output logic inj_named_out_1755007771723_49,
    output bit inj_out_1755007771723_660,
    output logic [7:0] inj_out_diff_m2_1755007771723_486,
    output int inj_out_port_1755007771723_128,
    output logic [7:0] inj_out_vec_1755007771722_266,
    output logic [7:0] inj_var_out_m2_1755007771723_331,
    output logic [31:0] inj_wide_data_out_1755007771723_855
);
    // BEGIN: Module_IfNoneParam_ts1755007771723
    // BEGIN: expr_postsub_comb_ts1755007771723
    logic [7:0] var_m2_ts1755007771723;
        // BEGIN: module_using_package_param_ts1755007771723
        assign inj_wide_data_out_1755007771723_855 = inj_wide_data_in_1755007771723_555;
        // END: module_using_package_param_ts1755007771723

        // BEGIN: mod_default_disable_ts1755007771723
        assign inj_out_1755007771723_660 = inj_enable_in_1755007771723_203;
        // END: mod_default_disable_ts1755007771723

    always_comb begin
        var_m2_ts1755007771723 = inj_in_vec_1755007771722_751;
        inj_out_diff_m2_1755007771723_486 = (var_m2_ts1755007771723--) - inj_sub_val_m2_1755007771723_800;
        inj_var_out_m2_1755007771723_331 = var_m2_ts1755007771723;
    end
    // END: expr_postsub_comb_ts1755007771723

    assign inj_out_port_1755007771723_128 = inj_in_port_1755007771723_429;
    // END: Module_IfNoneParam_ts1755007771723

    module_with_param module_with_param_inst_1755007771723_592 (
        .in(inj_in_1755007771723_163),
        .named_out(inj_named_out_1755007771723_49)
    );
    SimpleLoopExample SimpleLoopExample_inst_1755007771722_9781 (
        .in_vec(inj_in_vec_1755007771722_751),
        .out_vec(inj_out_vec_1755007771722_266)
    );
endmodule

