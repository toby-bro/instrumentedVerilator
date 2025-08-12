package util_pkg;
    typedef struct packed {
        logic [31:0] data;
        logic [3:0]  tag;
    } t_packet;
    function automatic logic [31:0] popcount32 (logic [31:0] word);
        integer i;
        popcount32 = 0;
        for (i = 0; i < 32; i++) begin
            popcount32 = popcount32 + word[i];
        end
    endfunction
endpackage
module arithmetic_unit #(
    parameter WIDTH = 8
) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    input  logic             sel,
    output logic [WIDTH-1:0] y
);
    always_comb begin
        if (sel)
            y = a + b;
        else
            y = a - b;
    end
endmodule
module struct_pipeline (
    input  util_pkg::t_packet in_pkt,
    output util_pkg::t_packet out_pkt
);
    import util_pkg::*;
    t_packet stage1, stage2;
    always_comb begin
        stage1       = in_pkt;
        stage1.data  = in_pkt.data + 1;
        stage2       = stage1;
        stage2.data  = stage1.data ^ {28'h0, stage1.tag};
        out_pkt      = stage2;
    end
endmodule
module enum_fsm (
    input  logic clk,
    input  logic reset_n,
    input  logic in_sig,
    output logic state_o
);
    typedef enum logic [1:0] {S0, S1, S2} state_t;
    state_t state, next_state;
    always_comb begin
        unique case (state)
            S0: next_state = in_sig ? S1 : S0;
            S1: next_state = in_sig ? S2 : S0;
            S2: next_state = in_sig ? S2 : S0;
            default: next_state = S0;
        endcase
    end
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            state <= S0;
        else
            state <= next_state;
    end
    assign state_o = state[0];
    property never_invalid;
        @(posedge clk) disable iff (!reset_n) state != 2'bxx;
    endproperty
    assert property (never_invalid);
endmodule
module bit_reverser #(
    parameter WIDTH = 16
) (
    input  logic [WIDTH-1:0] in_data,
    output logic [WIDTH-1:0] out_data
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_rev
            assign out_data[i] = in_data[WIDTH-1-i];
        end
    endgenerate
endmodule
module union_example (
    input  logic [31:0] in_word,
    output logic [31:0] out_word
);
    typedef union packed {
        logic [31:0]      word;
        logic [1:0][15:0] halfs;
        logic [3:0][7:0]  bytes;
    } u_multi;
    u_multi data_u;
    always_comb begin
        data_u.word = in_word;
        out_word    = { data_u.bytes[0],
                        data_u.bytes[1],
                        data_u.bytes[2],
                        data_u.bytes[3] };
    end
endmodule
interface simple_bus_if #(
    parameter WIDTH = 8
) ();
    logic [WIDTH-1:0] data;
    logic             valid;
    modport master (output data, output valid);
    modport slave  (input  data, input  valid);
endinterface
module bus_master #(
    parameter WIDTH = 8
) (
    input  logic             trigger,
    output logic             done,
    output logic [WIDTH-1:0] data_o,
    output logic             valid_o
);
    simple_bus_if #(WIDTH) m_if();
    always_comb begin
        if (trigger) begin
            m_if.data = WIDTH'(1);
            m_if.valid = 1;
            data_o  = m_if.data;
            valid_o = m_if.valid;
            done    = 1;
        end else begin
            m_if.data = '0;
            m_if.valid = 0;
            data_o  = m_if.data;
            valid_o = m_if.valid;
            done    = 0;
        end
    end
endmodule
module bit_counter (
    input  logic [31:0] word_in,
    output logic [5:0]  bitcount_out
);
    import util_pkg::popcount32;
    always_comb begin
        bitcount_out = popcount32(word_in)[5:0];
    end
endmodule
