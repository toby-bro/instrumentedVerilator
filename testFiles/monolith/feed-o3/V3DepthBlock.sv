module nested_if_mod (
    input  logic [7:0] in_data,
    output logic       out_flag
);
    function automatic logic deep_if_calc (input logic [7:0] d);
        logic result;
        begin
            if (d[7]) begin
                if (d[6]) begin
                    if (d[5]) begin
                        if (d[4]) begin
                            if (d[3]) begin
                                if (d[2]) begin
                                    if (d[1]) begin
                                        if (d[0]) begin
                                            result = 1;
                                        end else begin
                                            result = 0;
                                        end
                                    end else begin
                                        result = 0;
                                    end
                                end else begin
                                    result = 0;
                                end
                            end else begin
                                result = 0;
                            end
                        end else begin
                            result = 0;
                        end
                    end else begin
                        result = 0;
                    end
                end else begin
                    result = 0;
                end
            end else begin
                result = 0;
            end
            deep_if_calc = result;
        end
    endfunction
    always_comb out_flag = deep_if_calc(in_data);
endmodule
module nested_for_mod (
    input  logic [3:0] in_val,
    output logic [7:0] out_sum
);
    function automatic logic [7:0] nested_sum (input logic [3:0] n);
        logic [7:0] acc;
        begin
            acc = 0;
            for (int i = 0; i < 4; ++i) begin
                for (int j = 0; j < 4; ++j) begin
                    for (int k = 0; k < 4; ++k) begin
                        acc += n + i + j + k;
                    end
                end
            end
            nested_sum = acc;
        end
    endfunction
    always_comb out_sum = nested_sum(in_val);
endmodule
module nested_case_mod (
    input  logic [3:0] sel,
    output logic       out_bit
);
    function automatic logic decode (input logic [3:0] s);
        logic inner;
        begin
            case (s[3:2])
                2'b00: inner = 0;
                2'b01: begin
                    case (s[1:0])
                        2'b00: inner = 0;
                        2'b01: inner = 1;
                        2'b10: inner = 1;
                        default: inner = 0;
                    endcase
                end
                2'b10: begin
                    case (s[1:0])
                        2'b00: inner = 1;
                        2'b01: inner = 0;
                        2'b10: inner = 1;
                        default: inner = 0;
                    endcase
                end
                default: inner = 0;
            endcase
            decode = inner;
        end
    endfunction
    always_comb out_bit = decode(sel);
endmodule
module class_compute_mod (
    input  logic [7:0] in_byte,
    output logic [7:0] out_byte
);
    class adder_c;
        function automatic logic [7:0] add4 (input logic [7:0] a);
            return a + 8'd4;
        endfunction
    endclass
    always_comb begin
        adder_c c = new();
        out_byte = c.add4(in_byte);
    end
endmodule
module jump_block_mod (
    input  logic [5:0] in_cnt,
    output logic [5:0] out_cnt
);
    function automatic logic [5:0] loop_break (input logic [5:0] v);
        logic [5:0] val;
        begin
            val = 0;
            for (int i = 0; i < 6; ++i) begin
                val += i;
                if (v == i) begin
                    break;
                end
            end
            loop_break = val;
        end
    endfunction
    always_comb out_cnt = loop_break(in_cnt);
endmodule
