interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module FunctionTaskMod (
    input logic [7:0] data_in,
    output logic is_even
);
    function automatic bit check_even(input logic [7:0] v);
        check_even = ~v[0];
    endfunction
    task automatic dummy_task(input logic [7:0] v);
        int tmp;
        tmp = v;
    endtask
    assign is_even = check_even(data_in);
endmodule

module cu_timeunit_mod (
    input logic clk,
    output logic reset
);
    logic internal_sig;
    always_ff @(posedge clk) begin
        reset <= 1'b0;
        internal_sig = clk;
    end
endmodule

module nets_alias_clocking (
    input logic i_clk,
    input logic i_data_sync,
    input logic i_reg_data,
    input wire i_wire_data,
    output logic o_reg_out,
    output wire o_wire_out
);
    wire  w_internal;
    logic r_internal;
    assign w_internal  = i_wire_data & i_reg_data;
    assign o_wire_out  = w_internal;
    always_ff @(posedge i_clk) r_internal <= i_data_sync;
    assign o_reg_out = r_internal;
endmodule

module unsupported_cond_expr (
    input bit condition_m10,
    input logic [7:0] in_val_m10,
    output logic [7:0] out_val_m10
);
    logic [7:0] var_m10;
    always_comb begin
        var_m10 = in_val_m10;
        out_val_m10 = condition_m10 ? var_m10 : var_m10;
        var_m10++;
    end
endmodule

module wide_ops_deep (
    input logic [63:0] wide_a,
    input logic [63:0] wide_b,
    input logic [63:0] wide_c,
    output logic [63:0] wide_out
);
    assign wide_out = (((wide_a + wide_b) ^ wide_c) & (~wide_a | wide_b)) + (wide_c >>> 5);
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755007802885_270,
    input logic [3:0] inj_a_1755007802888_416,
    input int inj_b_1755007802885_23,
    input bit inj_condition_m10_1755007802884_972,
    input logic [7:0] inj_in_val_m10_1755007802884_780,
    input wire [63:0] inj_wide_a_1755007802886_365,
    input logic [63:0] inj_wide_a_1755007802889_477,
    input wire [63:0] inj_wide_b_1755007802886_205,
    input logic [63:0] inj_wide_b_1755007802889_433,
    input logic [63:0] inj_wide_c_1755007802889_438,
    input wire reset,
    output wire [127:0] inj_concat_out_1755007802886_698,
    output logic inj_is_even_1755007802884_144,
    output logic inj_o_reg_out_1755007802886_804,
    output wire inj_o_wire_out_1755007802886_433,
    output logic inj_out_a_1755007802885_266,
    output int inj_out_b_1755007802885_928,
    output logic [7:0] inj_out_val_m10_1755007802884_180,
    output logic inj_out_valid_status_1755007802884_152,
    output wire [7:0] inj_reduce_xor_out_1755007802886_70,
    output logic inj_reset_1755007802887_285,
    output logic [63:0] inj_wide_out_1755007802889_52,
    output wire [63:0] inj_wide_sum_1755007802886_135,
    output logic [3:0] inj_y_1755007802888_51
);
    // BEGIN: module_assign_blocking_ts1755007802884
    // BEGIN: ModuleBasic_ts1755007802885
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c_ts1755007802885;
    int   d_ts1755007802885;
    always_comb begin
        logic temp_v_ts1755007802885;
            wide_ops_deep wide_ops_deep_inst_1755007802889_4184 (
                .wide_out(inj_wide_out_1755007802889_52),
                .wide_a(inj_wide_a_1755007802889_477),
                .wide_b(inj_wide_b_1755007802889_433),
                .wide_c(inj_wide_c_1755007802889_438)
            );
            // BEGIN: AlwaysCombInvert_ts1755007802888
            always_comb inj_y_1755007802888_51 = ~inj_a_1755007802888_416;
            // END: AlwaysCombInvert_ts1755007802888

            cu_timeunit_mod cu_timeunit_mod_inst_1755007802887_2215 (
                .clk(clk),
                .reset(inj_reset_1755007802887_285)
            );
            // BEGIN: wide_bus_ops_ts1755007802886
            assign inj_wide_sum_1755007802886_135 = inj_wide_a_1755007802886_365 + inj_wide_b_1755007802886_205;
            assign inj_reduce_xor_out_1755007802886_70 = ^inj_wide_a_1755007802886_365[63:0];
            assign inj_concat_out_1755007802886_698 = {inj_wide_a_1755007802886_365, inj_wide_b_1755007802886_205};
            // END: wide_bus_ops_ts1755007802886

            nets_alias_clocking nets_alias_clocking_inst_1755007802886_5522 (
                .i_data_sync(temp_v_ts1755007802885),
                .i_reg_data(inj_a_1755007802885_270),
                .i_wire_data(reset),
                .o_reg_out(inj_o_reg_out_1755007802886_804),
                .o_wire_out(inj_o_wire_out_1755007802886_433),
                .i_clk(clk)
            );
        temp_v_ts1755007802885 = d_ts1755007802885;
        c_ts1755007802885      = temp_v_ts1755007802885;
    end
    assign inj_out_a_1755007802885_266 = inj_a_1755007802885_270;
    assign d_ts1755007802885     = inj_b_1755007802885_23;
    assign inj_out_b_1755007802885_928 = d_ts1755007802885 + P1 + LP1;
    // END: ModuleBasic_ts1755007802885

    FunctionTaskMod FunctionTaskMod_inst_1755007802884_1994 (
        .is_even(inj_is_even_1755007802884_144),
        .data_in(inj_in_val_m10_1755007802884_780)
    );
    my_if vif_inst();
    always_comb begin
        vif_inst.data = inj_in_val_m10_1755007802884_780;
        vif_inst.valid = 1'b1;
        vif_inst.ready = 1'b0;
        inj_out_valid_status_1755007802884_152 = vif_inst.valid;
    end
    // END: module_assign_blocking_ts1755007802884

    unsupported_cond_expr unsupported_cond_expr_inst_1755007802884_2357 (
        .condition_m10(inj_condition_m10_1755007802884_972),
        .in_val_m10(inj_in_val_m10_1755007802884_780),
        .out_val_m10(inj_out_val_m10_1755007802884_180)
    );
endmodule

