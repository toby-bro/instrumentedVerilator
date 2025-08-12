module arithmetic_unit #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in_a,
    input  logic [WIDTH-1:0] in_b,
    input  logic             add_nsub,
    output logic [WIDTH-1:0] out_result
);
    always_comb begin
        if (add_nsub)
            out_result = in_a + in_b;
        else
            out_result = in_a - in_b;
    end
endmodule
module simple_fsm (
    input  logic clk,
    input  logic rst_n,
    input  logic start,
    output logic done
);
    typedef enum logic [1:0] {IDLE, BUSY, DONE} state_t;
    state_t state, next_state;
    always_comb begin
        next_state = state;
        case (state)
            IDLE: if (start) next_state = BUSY;
            BUSY: next_state = DONE;
            DONE: next_state = IDLE;
            default: next_state = IDLE;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end
    assign done = (state == DONE);
endmodule
module struct_union_example (
    input  logic [31:0] in_word,
    output logic [7:0]  out_byte0
);
    typedef struct packed {
        logic [7:0] b0;
        logic [7:0] b1;
        logic [7:0] b2;
        logic [7:0] b3;
    } word_t;
    typedef union packed {
        word_t         w;
        logic [31:0]   dw;
    } access_t;
    access_t u;
    always_comb begin
        u.dw = in_word;
        out_byte0 = u.w.b0;
    end
endmodule
module class_example (
    input  logic clk,
    input  logic rst,
    input  logic in_valid,
    output logic out_valid
);
    class counter_c;
        int unsigned cnt;
        function void inc();
            cnt++;
        endfunction
    endclass
    counter_c c;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            c = new();
            c.cnt = 0;
            out_valid <= 0;
        end else begin
            if (in_valid) begin
                if (c == null)
                    c = new();
                c.inc();
                out_valid <= 1;
            end else begin
                out_valid <= 0;
            end
        end
    end
endmodule
module assertion_example (
    input  logic clk,
    input  logic in_signal,
    output logic pass
);
    assign pass = in_signal;
    property stable_p;
        $stable(in_signal);
    endproperty
    assert property (@(posedge clk) stable_p);
endmodule
module type_param_demo #(
    type T = logic [7:0]
) (
    input  T in_data,
    output T out_data
);
    assign out_data = in_data;
endmodule
module cover_example (
    input  logic clk,
    input  logic [3:0] in_val,
    output logic [3:0] out_val
);
    covergroup cg @(posedge clk);
        coverpoint in_val;
    endgroup
    cg cg_i = new();
    always_ff @(posedge clk) begin
        out_val <= in_val;
        cg_i.sample();
    end
endmodule
