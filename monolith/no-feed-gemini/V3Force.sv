module ForceTest_BasicSingleBit (
    input logic in_a,
    input logic in_b,
    output logic out_s
);
    logic forceable single_bit_var;
    logic temp_logic;
    always_comb begin
        temp_logic = in_b;
        force single_bit_var = in_a;
    end
    always_comb begin
        out_s = single_bit_var;
        release single_bit_var;
    end
endmodule
module ForceTest_MultiBitRanged (
    input logic [3:0] in_val,
    input logic in_en,
    output logic [3:0] out_data
);
    logic forceable [3:0] multi_bit_data;
    logic [3:0] intermediate_val;
    always_comb begin
        intermediate_val = in_val | {in_en, in_en, in_en, in_en};
        force multi_bit_data[1:0] = in_val[1:0];
        force multi_bit_data = intermediate_val & ~in_val;
    end
    always_comb begin
        out_data = multi_bit_data;
        release multi_bit_data[2:0];
        release multi_bit_data;
    end
endmodule
module ForceTest_ContinuouslyDriven (
    input logic in_a,
    input logic in_b,
    output logic out_c
);
    wire forceable driven_wire;
    assign driven_wire = in_a ^ in_b;
    logic temp_logic_c;
    always_comb begin
        force driven_wire = in_a;
    end
    always_comb begin
        temp_logic_c = driven_wire;
        release driven_wire;
        out_c = temp_logic_c;
    end
endmodule
module ForceTest_InFunctionTaskLogic (
    input logic [7:0] in_data,
    input logic in_ctrl,
    output logic [7:0] out_sum
);
    logic forceable [7:0] internal_reg;
    function automatic logic [7:0] calculate_sum(logic [7:0] val1, logic [7:0] val2);
        logic [7:0] temp_func_var;
        temp_func_var = internal_reg;
        return val1 + val2 + temp_func_var;
    endfunction
    task automatic update_internal(logic [7:0] new_val);
        internal_reg = new_val;
        force internal_reg = {8{in_ctrl}} | new_val;
    endtask
    always_comb begin
        update_internal(in_data);
        out_sum = calculate_sum(in_data, internal_reg);
        release internal_reg;
    end
endmodule
module ForceTest_MixedTypesAndExpr (
    input logic in_x,
    input bit in_y,
    input signed [7:0] in_z,
    output logic out_result
);
    logic forceable [1:0] s_logic_2bit;
    bit forceable s_bit_1bit;
    signed logic forceable [7:0] s_signed_8bit;
    logic [7:0] intermediate_val_mix;
    logic [1:0] intermediate_2bit_mix;
    always_comb begin
        intermediate_val_mix = s_signed_8bit + in_z;
        intermediate_2bit_mix = {s_bit_1bit, in_x};
        force s_signed_8bit = (in_z >>> 1) + (s_logic_2bit[0] ? 8'd10 : 8'd20);
        force s_bit_1bit = in_x & in_y;
        force s_logic_2bit = {in_x, in_y};
        out_result = s_bit_1bit ^ s_logic_2bit[1] ^ (s_signed_8bit[0]);
    end
    always_comb begin
        release s_bit_1bit;
        release s_logic_2bit;
        s_signed_8bit = 8'd55;
    end
endmodule
