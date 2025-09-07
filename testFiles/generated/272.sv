module Comb_IfElse (
    input wire condition,
    input wire [15:0] value1,
    input wire [15:0] value2,
    output reg [15:0] result_val
);
    always_comb begin
        if (condition) begin
            result_val = value1;
        end else begin
            result_val = value2;
        end
    end
endmodule

module local_not_allowed_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module module_with_params #(
    parameter integer DATA_WIDTH = 8
) (
    input wire [7:0] param_in,
    output wire [7:0] param_out
);
    assign param_out = param_in;
endmodule

module snippet (
    input wire clk,
    input int inj_in_val_1755007845470_490,
    input wire [7:0] inj_param_in_1755007845470_973,
    input wire [15:0] inj_value1_1755007845471_190,
    input wire [15:0] inj_value2_1755007845471_153,
    input wire reset,
    output int inj_out_val_1755007845470_839,
    output int inj_out_val_1755007845471_337,
    output wire [7:0] inj_param_out_1755007845470_92,
    output reg [15:0] inj_result_val_1755007845471_627
);
    // BEGIN: local_not_allowed_diag_mod_ts1755007845471
    assign inj_out_val_1755007845471_337 = inj_in_val_1755007845470_490;
    // END: local_not_allowed_diag_mod_ts1755007845471

    Comb_IfElse Comb_IfElse_inst_1755007845471_8440 (
        .result_val(inj_result_val_1755007845471_627),
        .condition(clk),
        .value1(inj_value1_1755007845471_190),
        .value2(inj_value2_1755007845471_153)
    );
    module_with_params module_with_params_inst_1755007845470_4436 (
        .param_out(inj_param_out_1755007845470_92),
        .param_in(inj_param_in_1755007845470_973)
    );
    local_not_allowed_diag_mod local_not_allowed_diag_mod_inst_1755007845470_9598 (
        .in_val(inj_in_val_1755007845470_490),
        .out_val(inj_out_val_1755007845470_839)
    );
endmodule

