interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module ModuleBasic (
    input logic a,
    input int b,
    output logic out_a,
    output int out_b
);
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c;
    int   d;
    always_comb begin
        logic temp_v;
        temp_v = d;
        c      = temp_v;
    end
    assign out_a = a;
    assign d     = b;
    assign out_b = d + P1 + LP1;
endmodule

module ModuleHierarchy_High #(
    parameter int SEL_PARAM = 6
) (
    input logic [3:0] data_in,
    input int sel_in,
    output logic [7:0] data_out
);
    ModuleBasic m1 (
        .a      (1'b1),
        .b      (sel_in),
        .out_a  (),
        .out_b  ( )
    );
    if (SEL_PARAM > 5) begin : gen_high
        int high_data;
        ModuleBasic m_high (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (high_data)
        );
    end else begin : gen_low
        int low_data;
        ModuleBasic m_low (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (low_data)
        );
    end
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
        logic [1:0] sub_in;
        assign sub_in = data_in[i*2 +: 2];
        int temp_int;
        ModuleBasic m_inst (
            .a      (1'b0),
            .b      (int'(sub_in)),
            .out_a  (),
            .out_b  (temp_int)
        );
        assign data_out[i*4 +: 4] = temp_int[3:0];
    end
endmodule

module always_comb_assign (
    input logic [15:0] in,
    output logic [15:0] out
);
    always_comb begin
        out = in;
    end
endmodule

module mod_split_nested (
    input logic clk,
    input logic cond1,
    input logic cond2,
    input logic [7:0] data_in,
    input logic reset,
    output logic [7:0] out_nested_a,
    output logic [7:0] out_nested_b
);
    logic [7:0]  split_nested_var;
    logic [7:0] other_nested_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_nested_var <= 8'b0;
            other_nested_var <= 8'b0;
        end else begin
            split_nested_var <= 8'h11; 
            other_nested_var <= 8'h22; 
            if (cond1) begin
                split_nested_var <= data_in + 10;
                other_nested_var <= data_in + 20;
                if (cond2) begin
                    split_nested_var <= data_in + 100;
                    other_nested_var <= data_in + 200;
                end
            end else begin
                split_nested_var <= data_in - 10;
                other_nested_var <= data_in - 20;
            end
        end
    end
    always_comb begin
        out_nested_a = split_nested_var;
        out_nested_b = other_nested_var;
    end
endmodule

module module_latch (
    input wire [7:0] in_latch_data,
    input wire in_latch_en,
    output reg [7:0] out_latch_reg
);
    always_latch begin
    if (in_latch_en) begin
        out_latch_reg = in_latch_data;
    end
    end
endmodule

module primitive_example (
    input logic i_p1,
    input logic i_p2,
    output logic o_p_and,
    output logic o_p_xor
);
    and (o_p_and, i_p1, i_p2);
    xor (o_p_xor, i_p1, i_p2);
endmodule

module split_inputs_outputs_only (
    input logic [7:0] in_val_a_l,
    input logic [7:0] in_val_b_l,
    output logic [8:0] out_val_c_l,
    output logic [7:0] out_val_d_l
);
    always @(*) begin
        out_val_c_l = in_val_a_l + in_val_b_l;
        out_val_d_l = in_val_a_l - in_val_b_l;
    end
endmodule

module virtual_interface_lookup_mod (
    input logic dummy_in,
    input logic [7:0] vif_data,
    input logic vif_valid,
    output logic dummy_out,
    output logic [7:0] out_data,
    output logic out_valid
);
    always_comb begin
        out_data  = vif_data;
        out_valid = vif_valid;
        dummy_out = dummy_in;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_dummy_in_1755007750714_839,
    input bit inj_enable_in_1755007750718_526,
    input logic [3:0] inj_i_addr_arr_1755007750714_494,
    input logic [3:0] inj_i_addr_sel_1755007750714_322,
    input logic [7:0] inj_in3_1755007750716_918,
    input logic [15:0] inj_in_1755007750731_330,
    input wire [7:0] inj_in_latch_data_1755007750719_50,
    input logic [2:0] inj_in_val_1755007750723_339,
    input int inj_sel_in_1755007750715_360,
    input logic [7:0] inj_vif_data_1755007750714_552,
    input logic inj_vif_valid_1755007750714_685,
    input wire reset,
    output logic [7:0] inj_data_out_1755007750715_310,
    output logic inj_data_out_1755007750722_460,
    output logic inj_dummy_out_1755007750714_651,
    output logic inj_o_1755007750717_143,
    output logic [7:0] inj_o_array_var_elem_1755007750714_211,
    output logic inj_o_p_and_1755007750716_592,
    output logic inj_o_p_xor_1755007750716_568,
    output logic inj_o_sel_var_bit_1755007750714_951,
    output logic [7:0] inj_out_1755007750716_661,
    output bit inj_out_1755007750718_240,
    output logic [7:0] inj_out_1755007750718_814,
    output logic [15:0] inj_out_1755007750731_438,
    output logic [7:0] inj_out_data_1755007750714_14,
    output reg [7:0] inj_out_latch_reg_1755007750719_184,
    output logic [7:0] inj_out_nested_a_1755007750714_315,
    output logic [7:0] inj_out_nested_b_1755007750714_401,
    output reg inj_out_res_1755007750723_517,
    output logic [8:0] inj_out_val_c_l_1755007750729_373,
    output logic [7:0] inj_out_val_d_l_1755007750729_709,
    output logic inj_out_valid_1755007750714_675,
    output logic inj_out_valid_1755007750725_164,
    output logic inj_q_1755007750727_553,
    output logic inj_task_output_valid_1755007750720_212
);
    // BEGIN: HandleOutOfBoundsRead_ts1755007750715
    parameter ARR_SIZE = 4;
    logic [7:0] my_array_ts1755007750715 [0:ARR_SIZE-1];
        // BEGIN: ModuleImplicitPort_ts1755007750725
        logic valid_ts1755007750725;
            always_comb_assign always_comb_assign_inst_1755007750731_5663 (
                .in(inj_in_1755007750731_330),
                .out(inj_out_1755007750731_438)
            );
            split_inputs_outputs_only split_inputs_outputs_only_inst_1755007750729_4713 (
                .in_val_b_l(inj_vif_data_1755007750714_552),
                .out_val_c_l(inj_out_val_c_l_1755007750729_373),
                .out_val_d_l(inj_out_val_d_l_1755007750729_709),
                .in_val_a_l(my_array_ts1755007750715)
            );
            // BEGIN: ModClockedResetReg_ts1755007750727
            always @(posedge clk or negedge reset) begin
            if (!reset) begin
                inj_q_1755007750727_553 <= 1'b0;
            end else begin
                inj_q_1755007750727_553 <= inj_vif_valid_1755007750714_685;
            end
            end
            // END: ModClockedResetReg_ts1755007750727

        assign valid_ts1755007750725 = |inj_vif_data_1755007750714_552;
        assign inj_out_valid_1755007750725_164 = valid_ts1755007750725;
        // END: ModuleImplicitPort_ts1755007750725

        // BEGIN: casez_xz_alt_ts1755007750723
        always_comb begin
            inj_out_res_1755007750723_517 = 1'b0;
            casez (inj_in_val_1755007750723_339)
                3'b1?z: inj_out_res_1755007750723_517 = 1'b1;
                3'b0z?: inj_out_res_1755007750723_517 = 1'b0;
                default: inj_out_res_1755007750723_517 = 1'b1;
            endcase
        end
        // END: casez_xz_alt_ts1755007750723

        // BEGIN: child_scalar_port_ts1755007750722
        assign inj_data_out_1755007750722_460 = inj_vif_valid_1755007750714_685;
        // END: child_scalar_port_ts1755007750722

        // BEGIN: module_task_write_ts1755007750720
        my_if task_vif_inst();
        task automatic update_vif_signals(input logic en, input logic [7:0] data_val,
            output logic [7:0] vif_data, output logic vif_valid, output logic vif_ready);
            if (en) begin
                vif_data = data_val;
                vif_valid = 1'b1;
                vif_ready = 1'b0;
            end else begin
                vif_data = 8'h0;
                vif_valid = 1'b0;
                vif_ready = 1'b1;
            end
        endtask
        always_comb begin
            update_vif_signals(inj_dummy_in_1755007750714_839, my_array_ts1755007750715, task_vif_inst.data, task_vif_inst.valid, task_vif_inst.ready);
            inj_task_output_valid_1755007750720_212 = task_vif_inst.valid;
        end
        // END: module_task_write_ts1755007750720

        module_latch module_latch_inst_1755007750719_9656 (
            .in_latch_en(clk),
            .out_latch_reg(inj_out_latch_reg_1755007750719_184),
            .in_latch_data(inj_in_latch_data_1755007750719_50)
        );
        // BEGIN: deep_logic_ts1755007750718
        assign inj_out_1755007750718_814 = (((inj_vif_data_1755007750714_552 & my_array_ts1755007750715) | (~inj_in3_1755007750716_918)) ^ (inj_vif_data_1755007750714_552 + my_array_ts1755007750715)) - (inj_in3_1755007750716_918 << 2);
        // END: deep_logic_ts1755007750718

        // BEGIN: mod_default_disable_ts1755007750718
        assign inj_out_1755007750718_240 = inj_enable_in_1755007750718_526;
        // END: mod_default_disable_ts1755007750718

        // BEGIN: child_module_v2_config_dummy_ts1755007750717
        assign inj_o_1755007750717_143 = inj_dummy_in_1755007750714_839 | inj_dummy_in_1755007750714_839; 
        // END: child_module_v2_config_dummy_ts1755007750717

        // BEGIN: bitwise_ops_ts1755007750716
        assign inj_out_1755007750716_661 = (my_array_ts1755007750715 & inj_vif_data_1755007750714_552) | (~inj_in3_1755007750716_918) ^ (my_array_ts1755007750715 << 2) >> 1;
        // END: bitwise_ops_ts1755007750716

        primitive_example primitive_example_inst_1755007750716_352 (
            .o_p_xor(inj_o_p_xor_1755007750716_568),
            .i_p1(inj_dummy_in_1755007750714_839),
            .i_p2(inj_vif_valid_1755007750714_685),
            .o_p_and(inj_o_p_and_1755007750716_592)
        );
        ModuleHierarchy_High ModuleHierarchy_High_inst_1755007750715_8787 (
            .sel_in(inj_sel_in_1755007750715_360),
            .data_out(inj_data_out_1755007750715_310),
            .data_in(inj_i_addr_arr_1755007750714_494)
        );
    assign my_array_ts1755007750715[0] = 8'd10;
    assign my_array_ts1755007750715[1] = 8'd20;
    assign my_array_ts1755007750715[2] = 8'd30;
    assign my_array_ts1755007750715[3] = 8'd40;
    assign inj_o_sel_var_bit_1755007750714_951 = inj_vif_data_1755007750714_552[inj_i_addr_sel_1755007750714_322];
    assign inj_o_array_var_elem_1755007750714_211 = my_array_ts1755007750715[inj_i_addr_arr_1755007750714_494];
    // END: HandleOutOfBoundsRead_ts1755007750715

    mod_split_nested mod_split_nested_inst_1755007750714_8076 (
        .reset(reset),
        .out_nested_a(inj_out_nested_a_1755007750714_315),
        .out_nested_b(inj_out_nested_b_1755007750714_401),
        .clk(clk),
        .cond1(inj_dummy_in_1755007750714_839),
        .cond2(inj_vif_valid_1755007750714_685),
        .data_in(inj_vif_data_1755007750714_552)
    );
    virtual_interface_lookup_mod virtual_interface_lookup_mod_inst_1755007750714_5946 (
        .vif_valid(inj_vif_valid_1755007750714_685),
        .dummy_out(inj_dummy_out_1755007750714_651),
        .out_data(inj_out_data_1755007750714_14),
        .out_valid(inj_out_valid_1755007750714_675),
        .dummy_in(inj_dummy_in_1755007750714_839),
        .vif_data(inj_vif_data_1755007750714_552)
    );
endmodule

