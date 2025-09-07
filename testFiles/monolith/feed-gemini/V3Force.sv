module ForceWireLogicBits (
    input logic clk,
    input logic reset_n,
    output logic [7:0] out_logic_array_read,
    output logic out_logic_bit_read,
    output logic out_wire_val_read
);
    (* verilator_forceable *) logic [7:0] my_logic_array;
    (* verilator_forceable *) logic my_logic_bit;
    (* verilator_forceable *) wire my_wire_signal;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            my_logic_array <= 8'h00;
            my_logic_bit <= 1'b0;
        end else begin
            my_logic_array <= my_logic_array + 1;
            my_logic_bit <= ~my_logic_bit;
        end
    end
    assign my_wire_signal = my_logic_bit;
    final begin
        force my_logic_array = 8'hAA;
        force my_logic_bit = 1'b1;
        force my_wire_signal = 1'b0;
        release my_logic_array;
        release my_logic_bit;
        release my_wire_signal;
    end
    assign out_logic_array_read = my_logic_array;
    assign out_logic_bit_read = my_logic_bit;
    assign out_wire_val_read = my_wire_signal;
endmodule
module ForceNumericTypes (
    input logic clk,
    input int in_int_val,
    output real out_real_val_read,
    output int out_int_val_read
);
    (* verilator_forceable *) int my_integer_signal;
    (* verilator_forceable *) real my_real_signal;
    always_ff @(posedge clk) begin
        my_integer_signal <= in_int_val + 1;
    end
    assign my_real_signal = $itor(my_integer_signal) * 2.0;
    final begin
        force my_integer_signal = 12345;
        release my_integer_signal;
        force my_real_signal = 3.14159;
        release my_real_signal;
    end
    assign out_real_val_read = my_real_signal;
    assign out_int_val_read = my_integer_signal;
endmodule
module ForceComplexRHS (
    input logic clk,
    input logic [7:0] data_input,
    input logic [7:0] control_input,
    output logic [7:0] result_out
);
    (* verilator_forceable *) logic [7:0] primary_target_val;
    (* verilator_forceable *) logic [7:0] rhs_var_for_force;
    always_ff @(posedge clk) begin
        rhs_var_for_force <= control_input;
    end
    final begin
        force primary_target_val = rhs_var_for_force ^ 8'hFF;
        force rhs_var_for_force = data_input;
        release primary_target_val;
        release rhs_var_for_force;
    end
    assign result_out = primary_target_val;
endmodule
