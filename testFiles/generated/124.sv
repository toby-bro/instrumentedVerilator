module CombinationalLogic (
    input logic enable,
    input logic [3:0] val_a,
    input logic [3:0] val_b,
    output logic [3:0] result
);
    always_comb begin
        if (enable) begin
            result = val_a + val_b;
        end else begin
            result = 4'h0;
        end
    end
endmodule

module unreferenced_module (
    input logic unused_in,
    output logic unused_out
);
    assign unused_out = ~unused_in;
endmodule

module snippet (
    input wire clk,
    input logic inj_enable_1755007794488_694,
    input logic [3:0] inj_val_a_1755007794487_603,
    input logic [3:0] inj_val_b_1755007794487_510,
    input wire reset,
    output logic [3:0] inj_result_1755007794487_628,
    output logic inj_unused_out_1755007794488_492
);
    unreferenced_module unreferenced_module_inst_1755007794488_9834 (
        .unused_out(inj_unused_out_1755007794488_492),
        .unused_in(inj_enable_1755007794488_694)
    );
    CombinationalLogic CombinationalLogic_inst_1755007794488_7741 (
        .val_a(inj_val_a_1755007794487_603),
        .val_b(inj_val_b_1755007794487_510),
        .result(inj_result_1755007794487_628),
        .enable(inj_enable_1755007794488_694)
    );
endmodule

