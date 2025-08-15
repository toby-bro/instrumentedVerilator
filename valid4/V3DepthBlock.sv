module DeepIfElse(
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    logic [7:0] temp_val;
    always_comb begin
        temp_val = in_data;
        if (temp_val[0]) begin : d01
            temp_val = temp_val + 1;
            if (temp_val[1]) begin : d02
                temp_val = temp_val + 2;
                if (temp_val[2]) begin : d03
                    temp_val = temp_val + 3;
                    if (temp_val[3]) begin : d04
                        temp_val = temp_val + 4;
                        if (temp_val[4]) begin : d05
                            temp_val = temp_val + 5;
                            if (temp_val[5]) begin : d06
                                temp_val = temp_val + 6;
                                if (temp_val[6]) begin : d07
                                    temp_val = temp_val + 7;
                                    if (temp_val[7]) begin : d08
                                        temp_val = temp_val + 8;
                                        if (temp_val[0]) begin : d09
                                            temp_val = temp_val + 9;
                                            if (temp_val[1]) begin : d10
                                                temp_val = temp_val + 10;
                                                if (temp_val[2]) begin : d11
                                                    temp_val = temp_val + 11;
                                                    if (temp_val[3]) begin : d12
                                                        temp_val = temp_val + 12;
                                                        if (temp_val[4]) begin : d13
                                                            temp_val = temp_val + 13;
                                                            if (temp_val[5]) begin : d14
                                                                temp_val = temp_val + 14;
                                                                if (temp_val[6]) begin : d15
                                                                    temp_val = temp_val + 15;
                                                                end else begin
                                                                    temp_val = temp_val - 15;
                                                                end
                                                            end else begin
                                                                temp_val = temp_val - 14;
                                                            end
                                                        end else begin
                                                            temp_val = temp_val - 13;
                                                        end
                                                    end else begin
                                                        temp_val = temp_val - 12;
                                                    end
                                                end else begin
                                                    temp_val = temp_val - 11;
                                                end
                                            end else begin
                                                temp_val = temp_val - 10;
                                            end
                                        end else begin
                                            temp_val = temp_val - 9;
                                        end
                                    end else begin
                                        temp_val = temp_val - 8;
                                    end
                                end else begin
                                    temp_val = temp_val - 7;
                                end
                            end else begin
                                temp_val = temp_val - 6;
                            end
                        end else begin
                            temp_val = temp_val - 5;
                        end
                    end else begin
                        temp_val = temp_val - 4;
                    end
                end else begin
                    temp_val = temp_val - 3;
                end
            end else begin
                temp_val = temp_val - 2;
            end
        end else begin
            temp_val = temp_val - 1;
        end
        out_data = temp_val;
    end
endmodule
module DeepForLoop(
    input logic [7:0] in_dummy_input,
    output logic [7:0] out_sum
);
    logic [7:0] sum_reg;
    logic [7:0] i0, i1, i2, i3;
    always_comb begin
        sum_reg = 0;
        for (i0 = 0; i0 < 2; i0 = i0 + 1) begin
            for (i1 = 0; i1 < 2; i1 = i1 + 1) begin
                for (i2 = 0; i2 < 2; i2 = i2 + 1) begin
                    for (i3 = 0; i3 < 2; i3 = i3 + 1) begin
                        sum_reg = sum_reg + i0 + i1 + i2 + i3;
                        sum_reg = sum_reg % 100;
                    end
                end
            end
        end
        out_sum = sum_reg;
    end
endmodule
module DeepCase(
    input logic [3:0] in_sel_0,
    input logic [3:0] in_sel_1,
    input logic [3:0] in_sel_2,
    input logic [3:0] in_sel_3,
    output logic [7:0] out_result
);
    logic [7:0] temp_res;
    always_comb begin
        temp_res = 0;
        case (in_sel_0)
            0: begin
                case (in_sel_1)
                    0: begin
                        case (in_sel_2)
                            0: begin
                                case (in_sel_3)
                                    0: temp_res = 1;
                                    1: temp_res = 2;
                                    2: temp_res = 3;
                                    3: temp_res = 4;
                                    4: temp_res = 5;
                                    5: temp_res = 6;
                                    6: temp_res = 7;
                                    7: temp_res = 8;
                                    8: temp_res = 9;
                                    9: temp_res = 10;
                                    10: temp_res = 11;
                                    11: temp_res = 12;
                                    12: temp_res = 13;
                                    13: temp_res = 14;
                                    14: temp_res = 15;
                                    15: temp_res = 16;
                                    default: temp_res = 17;
                                endcase
                            end
                            1: temp_res = 100;
                            default: temp_res = 101;
                        endcase
                    end
                    1: temp_res = 200;
                    default: temp_res = 201;
                endcase
            end
            1: temp_res = 300;
            default: temp_res = 301;
        endcase
        out_result = temp_res;
    end
endmodule
module FunctionDepth (
    input logic [15:0] in_val,
    output logic [15:0] out_val
);
    function automatic [15:0] deep_func_calc (input [15:0] current_val);
        logic [15:0] temp_deep_val;
        temp_deep_val = current_val;
        if (temp_deep_val[0]) begin
            temp_deep_val = temp_deep_val + 1;
            if (temp_deep_val[1]) begin
                temp_deep_val = temp_deep_val + 2;
                if (temp_deep_val[2]) begin
                    temp_deep_val = temp_deep_val + 3;
                    if (temp_deep_val[3]) begin
                        temp_deep_val = temp_deep_val + 4;
                        if (temp_deep_val[4]) begin
                            temp_deep_val = temp_deep_val + 5;
                            if (temp_deep_val[5]) begin
                                temp_deep_val = temp_deep_val + 6;
                                if (temp_deep_val[6]) begin
                                    temp_deep_val = temp_deep_val + 7;
                                    if (temp_deep_val[7]) begin
                                        temp_deep_val = temp_deep_val + 8;
                                        if (temp_deep_val[8]) begin
                                            temp_deep_val = temp_deep_val + 9;
                                            if (temp_deep_val[9]) begin
                                                temp_deep_val = temp_deep_val + 10;
                                                if (temp_deep_val[10]) begin
                                                    temp_deep_val = temp_deep_val + 11;
                                                    if (temp_deep_val[11]) begin
                                                        temp_deep_val = temp_deep_val + 12;
                                                        if (temp_deep_val[12]) begin
                                                            temp_deep_val = temp_deep_val + 13;
                                                            if (temp_deep_val[13]) begin
                                                                temp_deep_val = temp_deep_val + 14;
                                                                if (temp_deep_val[14]) begin
                                                                    temp_deep_val = temp_deep_val + 15;
                                                                end else begin
                                                                    temp_deep_val = temp_deep_val - 15;
                                                                end
                                                            end else begin
                                                                temp_deep_val = temp_deep_val - 14;
                                                            end
                                                        end else begin
                                                            temp_deep_val = temp_deep_val - 13;
                                                        end
                                                    end else begin
                                                        temp_deep_val = temp_deep_val - 12;
                                                    end
                                                end else begin
                                                    temp_deep_val = temp_deep_val - 11;
                                                end
                                            end else begin
                                                temp_deep_val = temp_deep_val - 10;
                                            end
                                        end else begin
                                            temp_deep_val = temp_deep_val - 9;
                                        end
                                    end else begin
                                        temp_deep_val = temp_deep_val - 8;
                                    end
                                end else begin
                                    temp_deep_val = temp_deep_val - 7;
                                end
                            end else begin
                                temp_deep_val = temp_deep_val - 6;
                            end
                        end else begin
                            temp_deep_val = temp_deep_val - 5;
                        end
                    end else begin
                        temp_deep_val = temp_deep_val - 4;
                    end
                end else begin
                    temp_deep_val = temp_deep_val - 3;
                end
            end else begin
                temp_deep_val = temp_deep_val - 2;
            end
        end else begin
            temp_deep_val = temp_deep_val - 1;
        end
        return temp_deep_val;
    endfunction
    always_comb begin
        out_val = deep_func_calc(in_val);
    end
endmodule
class MyDeepClass;
    local int m_internal_value;
    function new(int initial_val);
        m_internal_value = initial_val;
    endfunction
    function automatic int instance_deep_method(input int factor);
        int result;
        result = m_internal_value * factor;
        if (result > 10) begin
            result = result + 1;
            if (result > 20) begin
                result = result + 2;
                if (result > 30) begin
                    result = result + 3;
                    if (result > 40) begin
                        result = result + 4;
                        if (result > 50) begin
                            result = result + 5;
                            if (result > 60) begin
                                result = result + 6;
                                if (result > 70) begin
                                    result = result + 7;
                                    if (result > 80) begin
                                        result = result + 8;
                                        if (result > 90) begin
                                            result = result + 9;
                                            if (result > 100) begin
                                                result = result + 10;
                                                if (result > 110) begin
                                                    result = result + 11;
                                                    if (result > 120) begin
                                                        result = result + 12;
                                                        if (result > 130) begin
                                                            result = result + 13;
                                                            if (result > 140) begin
                                                                result = result + 14;
                                                                if (result > 150) begin
                                                                    result = result + 15;
                                                                end else begin
                                                                    result = result - 15;
                                                                end
                                                            end else begin
                                                                result = result - 14;
                                                            end
                                                        end else begin
                                                            result = result - 13;
                                                        end
                                                    end else begin
                                                        result = result - 12;
                                                    end
                                                end else begin
                                                    result = result - 11;
                                                end
                                            end else begin
                                                result = result - 10;
                                            end
                                        end else begin
                                            result = result - 9;
                                        end
                                    end else begin
                                        result = result - 8;
                                    end
                                end else begin
                                    result = result - 7;
                                end
                            end else begin
                                result = result - 6;
                            end
                        end else begin
                            result = result - 5;
                        end
                    end else begin
                        result = result - 4;
                    end
                end else begin
                    result = result - 3;
                end
            end else begin
                result = result - 2;
            end
        end else begin
            result = result - 1;
        end
        return result;
    endfunction
    static function int static_deep_method(input int initial_val, input int factor);
        automatic int result;
        result = initial_val * factor;
        if (result > 10) begin
            result = result + 1;
            if (result > 20) begin
                result = result + 2;
                if (result > 30) begin
                    result = result + 3;
                    if (result > 40) begin
                        result = result + 4;
                        if (result > 50) begin
                            result = result + 5;
                            if (result > 60) begin
                                result = result + 6;
                                if (result > 70) begin
                                    result = result + 7;
                                    if (result > 80) begin
                                        result = result + 8;
                                        if (result > 90) begin
                                            result = result + 9;
                                            if (result > 100) begin
                                                result = result + 10;
                                                if (result > 110) begin
                                                    result = result + 11;
                                                    if (result > 120) begin
                                                        result = result + 12;
                                                        if (result > 130) begin
                                                            result = result + 13;
                                                            if (result > 140) begin
                                                                result = result + 14;
                                                                if (result > 150) begin
                                                                    result = result + 15;
                                                                end else begin
                                                                    result = result - 15;
                                                                end
                                                            end else begin
                                                                result = result - 14;
                                                            end
                                                        end else begin
                                                            result = result - 13;
                                                        end
                                                    end else begin
                                                        result = result - 12;
                                                    end
                                                end else begin
                                                    result = result - 11;
                                                end
                                            end else begin
                                                result = result - 10;
                                            end
                                        end else begin
                                            result = result - 9;
                                        end
                                    end else begin
                                        result = result - 8;
                                    end
                                end else begin
                                    result = result - 7;
                                end
                            end else begin
                                result = result - 6;
                            end
                        end else begin
                            result = result - 5;
                        end
                    end else begin
                        result = result - 4;
                    end
                end else begin
                    result = result - 3;
                end
            end else begin
                result = result - 2;
            end
        end else begin
            result = result - 1;
        end
        return result;
    endfunction
endclass
module ClassMethodDepth(
    input logic [7:0] in_init_val,
    input logic [7:0] in_factor,
    output logic [7:0] out_final_val
);
    logic [7:0] temp_out_val;
    always_comb begin
        temp_out_val = MyDeepClass::static_deep_method(in_init_val, in_factor);
        out_final_val = temp_out_val;
    end
endmodule
module InstanceClassMethodDepth(
    input logic [7:0] in_init_val,
    input logic [7:0] in_factor,
    output logic [7:0] out_final_val
);
    logic [7:0] temp_out_val;
    MyDeepClass my_obj;
    always_comb begin
        my_obj = new(in_init_val);
        temp_out_val = my_obj.instance_deep_method(in_factor);
        out_final_val = temp_out_val;
    end
endmodule
module MixedDepthBlock(
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic [7:0] out_c
);
    logic [7:0] temp_c;
    int k;
    always_comb begin
        temp_c = in_a;
        if (in_b[0]) begin
            temp_c = temp_c + 1;
            for (k = 0; k < 2; k = k + 1) begin
                temp_c = temp_c + k;
                case (in_b[1:0])
                    0: temp_c = temp_c * 2;
                    1: begin
                        temp_c = temp_c + 5;
                        if (in_b[2]) begin
                            temp_c = temp_c + 10;
                            begin
                                temp_c = temp_c + 100;
                                if (in_b[3]) begin
                                    temp_c = temp_c + 20;
                                    begin
                                        temp_c = temp_c + 200;
                                        for (int j = 0; j < 1; j = j + 1) begin
                                            temp_c = temp_c + j;
                                            case (in_b[4:3])
                                                0: temp_c = temp_c / 2;
                                                1: begin
                                                    temp_c = temp_c + 50;
                                                    if (in_b[5]) begin
                                                        temp_c = temp_c + 100;
                                                    end else temp_c = temp_c - 100;
                                                end
                                                default: temp_c = 1;
                                            endcase
                                        end
                                    end
                                end else temp_c = temp_c - 20;
                            end
                        end else temp_c = temp_c - 10;
                    end
                    default: temp_c = 0;
                endcase
            end
        end else begin
            temp_c = in_a - 1;
        end
        out_c = temp_c;
    end
endmodule
