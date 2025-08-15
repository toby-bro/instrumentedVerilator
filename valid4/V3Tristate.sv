module BasicTristate_BufIf (
    input logic in_data,
    input logic en_bufif1,
    input logic en_bufif0,
    input logic proc_in_data,
    output logic out_bufif1,
    output logic out_bufif0,
    output logic out_z_assign,
    output logic proc_out_data
);
    assign out_z_assign = 1'bz;
    bufif1 my_bufif1_gate (out_bufif1, in_data, en_bufif1);
    bufif0 my_bufif0_gate (out_bufif0, in_data, en_bufif0);
    always_comb begin
        proc_out_data = proc_in_data;
    end
endmodule
module SubModule_Hierarchical (
    input logic sub_input_a,
    input logic sub_enable_a,
    input logic sub_proc_in,
    inout wire sub_inout_b,
    output logic sub_output_c,
    output logic sub_proc_out
);
    assign sub_inout_b = sub_enable_a ? sub_input_a : 1'bz;
    assign sub_output_c = sub_input_a;
    always_comb begin
        sub_proc_out = sub_proc_in;
    end
endmodule
module HierarchicalTristate_Inout (
    input logic top_input_data,
    input logic top_enable_data,
    input logic top_proc_in,
    output logic top_output_result,
    output logic top_proc_out,
    inout tri [1:0] top_bidir_bus
);
    logic internal_signal_c;
    SubModule_Hierarchical sub_inst_slice (
        .sub_input_a(top_input_data),
        .sub_enable_a(top_enable_data),
        .sub_proc_in(top_proc_in),
        .sub_inout_b(top_bidir_bus[0]),
        .sub_output_c(internal_signal_c),
        .sub_proc_out(top_proc_out)
    );
    assign top_output_result = internal_signal_c;
    assign top_bidir_bus[1] = top_enable_data ? top_input_data : 1'bz;
    logic unused_read;
    assign unused_read = top_bidir_bus[1];
endmodule
module StrengthResolution_WiredNets (
    input logic strong_in,
    input logic weak_in,
    input logic pull_en,
    input logic wor_in1,
    input logic wor_in2,
    input logic wand_in1,
    input logic wand_in2,
    input logic proc_in_data,
    output logic strong_out,
    output logic weak_out,
    output logic pull_out,
    output logic wor_out,
    output logic wand_out,
    output logic proc_out_data
);
    wire strong_out_net;
    wire weak_out_net;
    wor wor_net;
    wand wand_net;
    tri pull_net;
    assign (strong1, strong0) strong_out_net = strong_in;
    assign strong_out = strong_out_net;
    assign (weak1, weak0) weak_out_net = weak_in;
    assign weak_out = weak_out_net;
    assign (strong1, strong0) pull_net = pull_en ? 1'b1 : 1'bz;
    pulldown(pull_net);
    assign wor_net = wor_in1;
    assign wor_net = wor_in2;
    assign wor_out = wor_net;
    assign wand_net = wand_in1;
    assign wand_net = wand_in2;
    assign wand_out = wand_net;
    assign pull_out = pull_net;
    always_comb begin
        proc_out_data = proc_in_data;
    end
endmodule
module TristateExpressions (
    input logic [3:0] in_a,
    input logic [3:0] in_b,
    input logic [1:0] sel_idx,
    input logic proc_in_data,
    output logic [7:0] out_concat_z,
    output logic [3:0] out_sel_z,
    output logic [3:0] out_extend_z_impl,
    output logic proc_out_data
);
    logic [3:0] z_nibble = 4'bzzzz;
    logic [7:0] wide_data_for_sel;
    logic [1:0] narrow_val_with_z = {1'b1, 1'bz};
    assign out_concat_z = {in_a, z_nibble};
    assign wide_data_for_sel = {z_nibble, in_b};
    assign out_sel_z = wide_data_for_sel[sel_idx +: 4];
    assign out_extend_z_impl = narrow_val_with_z;
    always_comb begin
        proc_out_data = proc_in_data;
    end
endmodule
module CaseEq_CountBits (
    input logic [3:0] in_a_4state,
    input logic [3:0] in_b_4state,
    input logic [1:0] case_ctrl_4state,
    input logic [7:0] count_val_4state,
    input logic proc_in_data,
    output logic out_caseeq_match,
    output logic out_neqcase_match,
    output logic out_eqwild_match,
    output logic out_neqwild_match,
    output logic [3:0] out_count_ones_z,
    output logic proc_out_data
);
    logic [3:0] pattern_z = 4'b1z01;
    localparam logic [3:0] pattern_x = 4'b1010;
    assign out_caseeq_match = (in_a_4state === pattern_z);
    assign out_neqcase_match = (in_b_4state !== pattern_z);
    assign out_eqwild_match = (in_a_4state ==? pattern_x);
    assign out_neqwild_match = (in_b_4state !=? pattern_x);
    assign out_count_ones_z = $countones(count_val_4state);
    always_comb begin
        proc_out_data = proc_in_data;
    end
endmodule
module ConditionalTristate_and_Unsup (
    input logic cond_ctrl,
    input logic in_data_cond,
    input logic in_z_cond,
    input logic proc_in_data,
    output logic out_cond_tri,
    output logic out_and_tri,
    output logic out_or_tri,
    output logic proc_out_data
);
    logic [0:0] z_val = 1'bz;
    assign out_cond_tri = cond_ctrl ? in_data_cond : z_val;
    assign out_and_tri = in_data_cond && z_val;
    assign out_or_tri = in_data_cond || z_val;
    always_comb begin
        proc_out_data = proc_in_data;
    end
endmodule
module ExplicitWarningTriggers (
    input logic in_a,
    input logic in_b,
    input logic proc_in_data,
    output logic out_c,
    output logic proc_out_data
);
    wire pull_net_warn;
    logic tri_cond_val;
    localparam logic [3:0] non_const_4state_rhs = 4'b1010;
    pullup(pull_net_warn);
    assign tri_cond_val = (in_a ? 1'bz : 1'b0);
    assign out_c = (tri_cond_val ? in_b : 1'b1);
    assign out_c = out_c || (in_b ==? non_const_4state_rhs);
    always_comb begin
        proc_out_data = proc_in_data;
    end
endmodule
