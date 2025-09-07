module ConditionalOps (
    input logic sel,
    input int val_false,
    input int val_true,
    output int out_val
);
    assign out_val = sel ? val_true : val_false;
endmodule

module comb_simple (
    input bit [7:0] in1,
    input bit [7:0] in2,
    output bit [7:0] out1,
    output bit [7:0] out2
);
    always @* begin
        out1 = in1 & in2;
        out2 = in1 | in2;
    end
endmodule

module func_macro_args (
    input int input_int,
    output int output_int
);
    `define ADD(a, b)       ((a) + (b))
    `define SUBTRACT(x, y)  ((x) - (y))
    localparam int P1_ADD = `ADD(10, 20);
    int p2_sub_var;
    always_comb begin
        p2_sub_var = `SUBTRACT(50, input_int);
    end
    assign output_int = P1_ADD + p2_sub_var;
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

module part_select_ops (
    input wire [31:0] wide_in,
    output wire [7:0] lower_byte_out,
    output wire [7:0] upper_byte_out
);
    wire [31:0] processed_wide;
    assign processed_wide = wide_in * 2;
    assign upper_byte_out = processed_wide[31:24];
    assign lower_byte_out = processed_wide[7:0];
endmodule

module rand_case_mod (
    input logic [2:0] selector,
    output logic [3:0] result_out
);
    always_comb begin
        case (selector)
            0: result_out = 4'h0;
            1: result_out = 4'h1;
            2: result_out = 4'hA;
            default: result_out = 4'hF;
        endcase
    end
endmodule

module snippet #(
    parameter integer DATA_WIDTH = 8
) (
    input wire clk,
    input logic inj_cond1_1755007849551_887,
    input logic inj_cond2_1755007849551_225,
    input logic [7:0] inj_data_in_1755007849551_306,
    input logic [3:0] inj_data_in_1755007849554_141,
    input bit [7:0] inj_in1_1755007849550_718,
    input bit [7:0] inj_in2_1755007849550_725,
    input int inj_input_int_1755007849550_134,
    input wire [7:0] inj_param_in_1755007849551_86,
    input logic [2:0] inj_selector_1755007849551_800,
    input int inj_val_true_1755007849552_311,
    input wire [31:0] inj_wide_in_1755007849552_474,
    input wire reset,
    output logic [7:0] inj_data_out_1755007849554_385,
    output wire [7:0] inj_lower_byte_out_1755007849552_820,
    output logic [7:0] inj_o_target_result_1755007849553_212,
    output bit [7:0] inj_out1_1755007849550_822,
    output bit [7:0] inj_out2_1755007849550_248,
    output logic [7:0] inj_out_nested_a_1755007849551_757,
    output logic [7:0] inj_out_nested_b_1755007849551_455,
    output int inj_out_val_1755007849552_980,
    output logic [7:0] inj_out_val_1755007849555_873,
    output int inj_output_int_1755007849550_935,
    output wire [7:0] inj_param_out_1755007849551_605,
    output logic [3:0] inj_result_out_1755007849551_301,
    output bit inj_system_status_clear_1755007849550_414,
    output wire [7:0] inj_upper_byte_out_1755007849552_71
);
    // BEGIN: PragmaResetDirectives_ts1755007849550
`ifdef SLANG_PRAGMA
`reset protect diagnostic
`endif
    // BEGIN: module_with_params_ts1755007849551
    // BEGIN: target_module_for_bind_ts1755007849553
    // BEGIN: ModSampledVarLogic_ts1755007849554
    logic [7:0] __Vsampled_state = 8'hAB; 
    logic [7:0] internal_reg_ts1755007849554;
        // BEGIN: generic_class_scope_diag_mod_ts1755007849555
        assign inj_out_val_1755007849555_873 = inj_data_in_1755007849551_306;
        // END: generic_class_scope_diag_mod_ts1755007849555

    always @(posedge clk) begin
    if (inj_data_in_1755007849554_141 == 4'd5) begin 
        internal_reg_ts1755007849554 <= __Vsampled_state + inj_data_in_1755007849554_141; 
    end else if (inj_data_in_1755007849554_141 > 4'd8) begin 
        internal_reg_ts1755007849554 <= {4'h0, inj_data_in_1755007849554_141} - 1; 
    end else begin
        internal_reg_ts1755007849554 <= 8'hFF;
    end
    end
    assign inj_data_out_1755007849554_385 = internal_reg_ts1755007849554;
    // END: ModSampledVarLogic_ts1755007849554

    always_comb inj_o_target_result_1755007849553_212 = inj_data_in_1755007849551_306 + 1;
    // END: target_module_for_bind_ts1755007849553

    part_select_ops part_select_ops_inst_1755007849552_6329 (
        .wide_in(inj_wide_in_1755007849552_474),
        .lower_byte_out(inj_lower_byte_out_1755007849552_820),
        .upper_byte_out(inj_upper_byte_out_1755007849552_71)
    );
    ConditionalOps ConditionalOps_inst_1755007849552_7054 (
        .val_true(inj_val_true_1755007849552_311),
        .out_val(inj_out_val_1755007849552_980),
        .sel(inj_cond1_1755007849551_887),
        .val_false(inj_input_int_1755007849550_134)
    );
    mod_split_nested mod_split_nested_inst_1755007849551_3793 (
        .cond1(inj_cond1_1755007849551_887),
        .cond2(inj_cond2_1755007849551_225),
        .data_in(inj_data_in_1755007849551_306),
        .reset(reset),
        .out_nested_a(inj_out_nested_a_1755007849551_757),
        .out_nested_b(inj_out_nested_b_1755007849551_455),
        .clk(clk)
    );
    rand_case_mod rand_case_mod_inst_1755007849551_5529 (
        .selector(inj_selector_1755007849551_800),
        .result_out(inj_result_out_1755007849551_301)
    );
    assign inj_param_out_1755007849551_605 = inj_param_in_1755007849551_86;
    // END: module_with_params_ts1755007849551

    func_macro_args func_macro_args_inst_1755007849550_7474 (
        .output_int(inj_output_int_1755007849550_935),
        .input_int(inj_input_int_1755007849550_134)
    );
assign inj_system_status_clear_1755007849550_414 = reset;
    // END: PragmaResetDirectives_ts1755007849550

    comb_simple comb_simple_inst_1755007849550_8224 (
        .out1(inj_out1_1755007849550_822),
        .out2(inj_out2_1755007849550_248),
        .in1(inj_in1_1755007849550_718),
        .in2(inj_in2_1755007849550_725)
    );
endmodule

