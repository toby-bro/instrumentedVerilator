//============================================================
//============================================================
module depth_nested_if #(
    parameter WIDTH = 8
) (
    input  logic [WIDTH-1:0] in_bus,
    output logic             out_flag
);
    always_comb begin : DEEP_NEST
        logic flag;
        flag = 1'b0;
        if (in_bus[0]) begin
            if (in_bus[1]) begin
                if (in_bus[2]) begin
                    if (in_bus[3]) begin
                        if (in_bus[4]) begin
                            if (in_bus[5]) begin
                                if (in_bus[6]) begin
                                    if (in_bus[7]) begin
                                        if (in_bus[0]) begin
                                            if (in_bus[1]) begin
                                                if (in_bus[2]) begin
                                                    if (in_bus[3]) begin
                                                        if (in_bus[4]) begin
                                                            if (in_bus[5]) begin
                                                                if (in_bus[6]) begin
                                                                    if (in_bus[7]) begin
                                                                        if (in_bus[0]) begin
                                                                            if (in_bus[1]) begin
                                                                                if (in_bus[2]) begin
                                                                                    if (in_bus[3]) begin
                                                                                        if (in_bus[4]) begin
                                                                                            if (in_bus[5]) begin
                                                                                                if (in_bus[6]) begin
                                                                                                    if (in_bus[7]) begin
                                                                                                        if (in_bus[0]) begin
                                                                                                            if (in_bus[1]) begin
                                                                                                                if (in_bus[2]) begin
                                                                                                                    if (in_bus[3]) begin
                                                                                                                        if (in_bus[4]) begin
                                                                                                                            if (in_bus[5]) begin
                                                                                                                                if (in_bus[6]) begin
                                                                                                                                    if (in_bus[7]) begin
                                                                                                                                        if (in_bus[0]) begin
                                                                                                                                            if (in_bus[1]) begin
                                                                                                                                                if (in_bus[2]) begin
                                                                                                                                                    if (in_bus[3]) begin
                                                                                                                                                        if (in_bus[4]) begin
                                                                                                                                                            if (in_bus[5]) begin
                                                                                                                                                                if (in_bus[6]) begin
                                                                                                                                                                    if (in_bus[7]) begin
                                                                                                                                                                        flag = 1'b1;
                                                                                                                                                                    end
                                                                                                                                                                end
                                                                                                                                                            end
                                                                                                                                                        end
                                                                                                                                                    end
                                                                                                                                                end
                                                                                                                                            end
                                                                                                                                        end
                                                                                                                                    end
                                                                                                                                end
                                                                                                                            end
                                                                                                                        end
                                                                                                                    end
                                                                                                                end
                                                                                                            end
                                                                                                        end
                                                                                                    end
                                                                                                end
                                                                                            end
                                                                                        end
                                                                                    end
                                                                                end
                                                                            end
                                                                        end
                                                                    end
                                                                end
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
        out_flag = flag;
    end
endmodule
//============================================================
//============================================================
module depth_expression_chain (
    input  logic [4:0] sel,
    input  logic [7:0] d0,  d1,  d2,  d3,  d4,
    input  logic [7:0] d5,  d6,  d7,  d8,  d9,
    output logic [7:0] y
);
    assign y = (sel ==  0) ? d0  :
               (sel ==  1) ? d1  :
               (sel ==  2) ? d2  :
               (sel ==  3) ? d3  :
               (sel ==  4) ? d4  :
               (sel ==  5) ? d5  :
               (sel ==  6) ? d6  :
               (sel ==  7) ? d7  :
               (sel ==  8) ? d8  :
               (sel ==  9) ? d9  :
               (sel == 10) ? d0  :
               (sel == 11) ? d1  :
               (sel == 12) ? d2  :
               (sel == 13) ? d3  :
               (sel == 14) ? d4  :
               (sel == 15) ? d5  :
               (sel == 16) ? d6  :
               (sel == 17) ? d7  :
               (sel == 18) ? d8  :
               (sel == 19) ? d9  :
               (sel == 20) ? d0  :
               (sel == 21) ? d1  :
               (sel == 22) ? d2  :
               (sel == 23) ? d3  :
               (sel == 24) ? d4  :
               (sel == 25) ? d5  :
               (sel == 26) ? d6  :
               (sel == 27) ? d7  :
               (sel == 28) ? d8  :
               (sel == 29) ? d9  :
               (sel == 30) ? d0  :
               (sel == 31) ? d1  : 8'h00;
endmodule
//============================================================
//============================================================
module depth_loop_break (
    input  logic clk,
    input  logic reset_n,
    output logic reached
);
    always_ff @(posedge clk or negedge reset_n) begin : LOOP_PROC
        integer i;
        if (!reset_n) begin
            reached <= 1'b0;
        end else begin
            reached <= 1'b0;
            for (i = 0; i < 32; i = i + 1) begin
                if (i == 17) begin
                    reached <= 1'b1;
                    break;
                end
            end
        end
    end
endmodule
//============================================================
//============================================================
module depth_function_call (
    input  logic [7:0] a,
    output logic [7:0] y
);
    function automatic void side_effectless (input logic [7:0] din);
        logic [7:0] sink;
        sink = din;       
    endfunction
    always_comb begin : FUNC_STMT_BLOCK
        side_effectless(a);      
        y = a + 8'd1;
    end
endmodule
//============================================================
//============================================================
module depth_static_function (
    input  logic        clk,
    input  logic        en,
    input  logic [15:0] in_val,
    output logic [15:0] accumulated
);
    function automatic logic [15:0] accumulate(input logic [15:0] val, input logic enable);
        static logic [15:0] acc = 16'h0000;
        if (enable) acc = acc + val;
        return acc;
    endfunction
    always_ff @(posedge clk) begin
        accumulated <= accumulate(in_val, en);
    end
endmodule
//============================================================
//============================================================
module depth_class_inst (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] y
);
    class math_c;
        bit [7:0] factor;
        function new(bit [7:0] f); factor = f; endfunction
        function bit [7:0] mul(bit [7:0] x); return x * factor; endfunction
    endclass
    always_comb begin : CLASS_PROC
        math_c m = new(8'd3);            
        y = m.mul(a ^ b);
    end
endmodule
//============================================================
//============================================================
module depth_struct_union (
    input  logic [7:0]  d_in,
    input  logic        sel,
    output logic [15:0] d_out
);
    typedef struct packed {
        logic [7:0] lo;
        logic [7:0] hi;
    } double_byte_s;
    typedef union packed {
        double_byte_s dub;
        logic [15:0]  raw;
    } mixed_u;
    always_comb begin : STRUCT_BLOCK
        mixed_u val;
        val.raw = 16'h0000;
        val.dub.lo = d_in;
        val.dub.hi = d_in ^ 8'hFF;
        d_out = sel ? val.raw : {val.dub.hi, val.dub.lo};
    end
endmodule
//============================================================
//============================================================
module depth_generate (
    input  logic [31:0] in_bus,
    output logic [31:0] out_bus
);
    logic [31:0] tmp [0:31];
    genvar g;
    generate
        for (g = 0; g < 32; g = g + 1) begin : GEN_BLOCK
            always_comb begin
                tmp[g] = {g[4:0], in_bus[g +: (32 - g > 0 ? 1 : 1)]};
            end
        end
    endgenerate
    assign out_bus = tmp[0] ^ tmp[1] ^ tmp[2] ^ tmp[3] ^ tmp[4] ^ tmp[5] ^
                     tmp[6] ^ tmp[7] ^ tmp[8] ^ tmp[9] ^ tmp[10] ^ tmp[11] ^
                     tmp[12] ^ tmp[13] ^ tmp[14] ^ tmp[15] ^ tmp[16] ^ tmp[17] ^
                     tmp[18] ^ tmp[19] ^ tmp[20] ^ tmp[21] ^ tmp[22] ^ tmp[23] ^
                     tmp[24] ^ tmp[25] ^ tmp[26] ^ tmp[27] ^ tmp[28] ^ tmp[29] ^
                     tmp[30] ^ tmp[31];
endmodule
//============================================================
//============================================================
module depth_combined (
    input  logic        clk,
    input  logic [3:0]  mode,
    input  logic [7:0]  in_a,
    input  logic [7:0]  in_b,
    output logic [7:0]  result
);
    logic [7:0] res_int;
    always_ff @(posedge clk) begin : COMBINED_PROC
        integer k;
        res_int <= 8'h00;
        for (k = 0; k < 4; k = k + 1) begin
            case (mode)
                4'd0: begin
                    res_int <= in_a + in_b;
                    if (in_a[0]) begin
                        if (in_b[0]) begin
                            if (in_a[1]) begin
                                if (in_b[1]) begin
                                    res_int <= res_int ^ 8'hAA;
                                end
                            end
                        end
                    end
                end
                4'd1: res_int <= in_a - in_b;
                4'd2: res_int <= in_a & in_b;
                4'd3: res_int <= in_a | in_b;
                default: res_int <= in_a ^ in_b;
            endcase
        end
    end
    assign result = res_int;
endmodule
