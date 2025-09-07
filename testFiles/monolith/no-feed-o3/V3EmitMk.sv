module adder_mod #(parameter WIDTH = 8)
(
    input  logic [WIDTH-1:0] a_i,
    input  logic [WIDTH-1:0] b_i,
    output logic [WIDTH:0]   sum_o
);
    always_comb begin
        sum_o = a_i + b_i;
    end
endmodule
module fsm_mod
(
    input  logic clk_i,
    input  logic rst_i,
    input  logic start_i,
    output logic done_o
);
    typedef enum logic [1:0] {S_IDLE, S_RUN, S_DONE} state_t;
    state_t state, next_state;
    always_comb begin
        unique case (state)
            S_IDLE: next_state = start_i ? S_RUN  : S_IDLE;
            S_RUN : next_state =           S_DONE;
            S_DONE: next_state = start_i ? S_RUN  : S_IDLE;
            default: next_state = S_IDLE;
        endcase
    end
    always_ff @(posedge clk_i or posedge rst_i) begin
        if (rst_i) state <= S_IDLE;
        else       state <= next_state;
    end
    assign done_o = (state == S_DONE);
endmodule
module struct_union_mod
(
    input  logic [31:0] in_i,
    output logic [15:0] out_o
);
    typedef struct packed {
        logic [7:0] lo;
        logic [7:0] hi;
    } bytes_t;
    typedef union packed {
        logic [15:0]   whole;
        bytes_t        split;
    } u_t;
    u_t u_data;
    always_comb begin
        u_data.whole   = in_i[15:0];
        out_o          = {u_data.split.hi, u_data.split.lo};
    end
endmodule
module class_inst_mod
(
    input  logic        clk_i,
    input  logic        rst_i,
    input  logic [3:0]  data_i,
    output logic [3:0]  data_o
);
    class holder_c;
        rand logic [3:0] value;
        function new(logic [3:0] v); value = v; endfunction
    endclass
    holder_c h;
    always_ff @(posedge clk_i or posedge rst_i) begin
        if (rst_i) begin
            data_o <= '0;
            h      = new('0);
        end else begin
            h      = new(data_i);
            data_o <= h.value;
        end
    end
endmodule
module latch_mod
(
    input  logic en_i,
    input  logic d_i,
    output logic q_o
);
    always_latch begin
        if (en_i) q_o <= d_i;
    end
endmodule
module gen_loop_mod #(parameter N = 4)
(
    input  logic [N-1:0] in_i,
    output logic [N-1:0] out_o
);
    genvar i;
    for (i = 0; i < N; i++) begin : GEN_REV
        assign out_o[i] = in_i[N-1-i];
    end
endmodule
module array_mod
(
    input  logic [7:0]  idx_i,
    input  logic        wr_i,
    input  logic [31:0] wdata_i,
    output logic [31:0] rdata_o
);
    logic [31:0] mem [0:255];
    always_ff @(posedge wr_i) begin
        mem[idx_i] <= wdata_i;
    end
    assign rdata_o = mem[idx_i];
endmodule
module assert_mod
(
    input  logic clk_i,
    input  logic rst_n_i,
    input  logic sig_i,
    output logic pass_o
);
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) pass_o <= 1'b0;
        else          pass_o <= sig_i;
    end
    property p_always_one;
        @(posedge clk_i) disable iff (!rst_n_i) sig_i == 1'b1;
    endproperty
    assert property (p_always_one);
endmodule
module cover_mod
(
    input  logic clk_i,
    input  logic rst_i,
    input  logic event_i,
    output logic dummy_o
);
    always_ff @(posedge clk_i or posedge rst_i) begin
        if (rst_i) dummy_o <= 1'b0;
        else       dummy_o <= event_i;
    end
    cover property (@(posedge clk_i) event_i);
endmodule
module priority_case_mod
(
    input  logic [1:0] sel_i,
    output logic       flag_o
);
    always_comb begin : PRIORITY_CASE
        priority case (sel_i)
            2'd0: flag_o = 1'b0;
            2'd1: flag_o = 1'b1;
            default: flag_o = 1'b0;
        endcase
    end
endmodule
module function_static_mod
(
    input  logic [15:0] a_i,
    input  logic [15:0] b_i,
    output logic [15:0] max_o
);
    function automatic logic [15:0] max_val(logic [15:0] x, y);
        if (x > y) max_val = x;
        else       max_val = y;
    endfunction
    assign max_o = max_val(a_i, b_i);
endmodule
module signed_unsigned_mod
(
    input  logic signed [7:0]  a_i,
    input  logic        [7:0]  b_i,
    output logic signed [8:0]  sum_o
);
    always_comb begin
        sum_o = a_i + $signed(b_i);
    end
endmodule
module shift_concat_mod
(
    input  logic [3:0] a_i,
    input  logic [3:0] b_i,
    output logic [7:0] y_o
);
    assign y_o = {a_i, b_i} << 1;
endmodule
module param_pipeline_mod #(parameter STAGES = 3)
(
    input  logic                  clk_i,
    input  logic [31:0]           in_i,
    output logic [31:0]           out_o
);
    logic [31:0] stage [0:STAGES];
    always_ff @(posedge clk_i) begin
        stage[0] <= in_i;
        for (int k = 1; k <= STAGES; k++) begin
            stage[k] <= stage[k-1];
        end
    end
    assign out_o = stage[STAGES];
endmodule
module mux_mod
(
    input  logic sel_i,
    input  logic a_i,
    input  logic b_i,
    output logic y_o
);
    assign y_o = sel_i ? a_i : b_i;
endmodule
module reduce_mod
(
    input  logic [15:0] data_i,
    output logic        parity_o
);
    assign parity_o = ^data_i;
endmodule
module matrix_mod
(
    input  logic [1:0][7:0] vec_a_i,
    input  logic [1:0][7:0] vec_b_i,
    output logic [1:0][7:0] vec_sum_o
);
    always_comb begin
        foreach (vec_sum_o[i]) begin
            vec_sum_o[i] = vec_a_i[i] + vec_b_i[i];
        end
    end
endmodule
module typedef_mod
(
    input  logic [7:0] in_i,
    output logic [7:0] out_o
);
    typedef logic [7:0] byte_t;
    byte_t tmp;
    always_comb begin
        tmp   = in_i;
        out_o = tmp;
    end
endmodule
module unique_case_mod
(
    input  logic [2:0] sel_i,
    output logic [7:0] y_o
);
    always_comb begin
        unique case (sel_i)
            3'd0: y_o = 8'h01;
            3'd1: y_o = 8'h02;
            3'd2: y_o = 8'h04;
            3'd3: y_o = 8'h08;
            3'd4: y_o = 8'h10;
            3'd5: y_o = 8'h20;
            default: y_o = 8'h00;
        endcase
    end
endmodule
module random_class_mod
(
    input  logic        clk_i,
    input  logic [7:0]  seed_i,
    output logic [7:0]  dout_o
);
    class rng_c;
        rand logic [7:0] val;
        function new(logic [7:0] s); val = s; endfunction
    endclass
    rng_c r;
    always_ff @(posedge clk_i) begin
        r      = new(seed_i);
        dout_o <= r.val;
    end
endmodule
module packed_array_mod
(
    input  logic [3:0][7:0] in_i,
    output logic [31:0]     out_o
);
    assign out_o = {in_i[3], in_i[2], in_i[1], in_i[0]};
endmodule
module for_generate_mod #(parameter WIDTH = 8, parameter DEPTH = 4)
(
    input  logic [WIDTH-1:0] data_i [DEPTH],
    output logic [WIDTH-1:0] data_o [DEPTH]
);
    genvar g;
    generate
        for (g = 0; g < DEPTH; g++) begin : GEN_PASS
            assign data_o[g] = data_i[g];
        end
    endgenerate
endmodule
module logic_vector_mod
(
    input  logic [7:0] in_i,
    output logic [7:0] rev_o
);
    function automatic logic [7:0] reverse_bits(logic [7:0] v);
        logic [7:0] r;
        for (int i = 0; i < 8; i++) begin
            r[i] = v[7-i];
        end
        return r;
    endfunction
    assign rev_o = reverse_bits(in_i);
endmodule
module nested_struct_mod
(
    input  logic [31:0] data_i,
    output logic [15:0] lo_o,
    output logic [15:0] hi_o
);
    typedef struct packed {
        logic [15:0] lo;
        logic [15:0] hi;
    } word_t;
    word_t w;
    always_comb begin
        w = data_i;
        lo_o = w.lo;
        hi_o = w.hi;
    end
endmodule
