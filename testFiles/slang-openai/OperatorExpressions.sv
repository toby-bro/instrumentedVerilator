//============================================================
//============================================================
module unary_ops_mod (
    input  logic        clk,
    input  logic        rst,
    input  logic signed [7:0] in_val,
    output logic signed [7:0] plus_out,
    output logic signed [7:0] minus_out,
    output logic signed [7:0] not_out,
    output logic               red_and,
    output logic               red_or,
    output logic               red_xor,
    output logic signed [7:0] pre_inc,
    output logic signed [7:0] post_inc
);
    logic signed [7:0] work;
    assign plus_out  = +in_val;
    assign minus_out = -in_val;
    assign not_out   = ~in_val;
    assign red_and   = &in_val;
    assign red_or    = |in_val;
    assign red_xor   = ^in_val;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            work <= '0;
            pre_inc  <= '0;
            post_inc <= '0;
        end
        else begin
            work    <= in_val;
            pre_inc <= ++work;     
            post_inc<= work++;     
        end
    end
endmodule
//============================================================
//============================================================
module binary_ops_mod (
    input  logic  [15:0] a,
    input  logic  [15:0] b,
    output logic  [15:0] add_sub_mul,
    output logic         eq_out,
    output logic         neq_out,
    output logic         gt_out,
    output logic         lt_out,
    output logic         logical_complex
);
    assign add_sub_mul = (a + b) * (a - b);
    assign eq_out  = (a === b);          
    assign neq_out = (a !== b);          
    assign gt_out = a > b;
    assign lt_out = a < b;
    assign logical_complex = a & 16'h00FF != 16'h0;
endmodule
//============================================================
//============================================================
module conditional_mod (
    input  logic [7:0] x,
    input  logic [7:0] y,
    input  logic       sel,
    output logic [7:0] result
);
    assign result = (sel && (x >= y)) ? x : y;
endmodule
//============================================================
//============================================================
module inside_mod (
    input  logic [7:0] value,
    output logic       match_simple,
    output logic       match_range
);
    assign match_simple = value inside {8'hFF, 8'hAA, 8'h55};
    assign match_range  = value inside { [8'h10:8'h1F], [8'h80:8'h8F] };
endmodule
//============================================================
//============================================================
module concat_rep_mod (
    input  logic  [7:0]  in0,
    input  logic  [3:0]  in1,
    output logic [15:0]  concat_out,
    output logic [11:0]  repl_out,
    output string        str_out
);
    assign concat_out = {in0, in1, 4'hF};
    assign repl_out   = {3{in1}};
    assign str_out = {"VAL=", in0};
endmodule
//============================================================
//============================================================
module stream_concat_mod (
    input  logic [31:0] data_in,
    output logic [31:0] data_swapped
);
    assign data_swapped = {<<8{data_in}};
endmodule
//============================================================
//============================================================
module value_range_mod (
    input  logic [15:0] test_val,
    output logic        in_tolerance
);
    typedef logic [15:0] word_t;
    word_t center = 16'd1000;
    word_t tol    = 16'd50;
    assign in_tolerance = test_val inside { center +- tol };
endmodule
//============================================================
//============================================================
module complex_feature_mod #(
    parameter int N = 4
)(
    input  logic             clk,
    input  logic [7:0]       bus_in [N],   
    input  logic [31:0]      data_in,
    output logic [31:0]      stream_out,
    output logic [N*8-1:0]   packed_concat
);
    assign packed_concat = {bus_in[3], bus_in[2], bus_in[1], bus_in[0]};
    assign stream_out = {<<8{ (data_in[0] ? data_in : ~data_in) }};
endmodule
//============================================================
//============================================================
module incdec_ff_mod (
    input  logic clk,
    input  logic rst_n,
    output logic [7:0] count_q
);
    logic [7:0] counter;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            counter <= '0;
        else begin
            ++counter;          
            counter--;          
        end
    end
    assign count_q = counter;
endmodule
