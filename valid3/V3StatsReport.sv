module stat_struct #(parameter WIDTH = 8) (
    input  logic              clk,
    input  logic [WIDTH-1:0]  i_data,
    output logic [WIDTH-1:0]  o_data,
    output logic [3:0]        o_tag
);
    typedef struct packed {
        logic [WIDTH-1:0] payload;
        logic [3:0]       tag;
    } packet_t;
    packet_t pkt;
    always_ff @(posedge clk) begin
        pkt.payload <= i_data;
        pkt.tag     <= 4'hA;
    end
    assign o_data = pkt.payload;
    assign o_tag  = pkt.tag;
endmodule
module stat_enum (
    input  logic        clk,
    input  logic [1:0]  mode,
    input  logic [7:0]  in_byte,
    output logic [7:0]  out_byte
);
    typedef enum logic [1:0] {IDLE = 2'b00, LOAD = 2'b01, EXEC = 2'b10, DONE = 2'b11} state_e;
    state_e state, next_state;
    always_comb begin
        unique case (mode)
            2'b00: next_state = IDLE;
            2'b01: next_state = LOAD;
            2'b10: next_state = EXEC;
            default: next_state = DONE;
        endcase
    end
    always_ff @(posedge clk) begin
        state <= next_state;
    end
    assign out_byte = (state == EXEC) ? in_byte : '0;
endmodule
module stat_class (
    input  logic        clk,
    input  logic [31:0] in_val,
    output logic [31:0] out_val
);
    class adder;
        function int add (input int a, input int b);
            return a + b;
        endfunction
    endclass
    adder add_inst;
    always_comb begin
        add_inst = new();
        if (clk) begin
            out_val = add_inst.add(in_val, 32'h1);
        end else begin
            out_val = in_val;
        end
    end
endmodule
module stat_generate #(
    parameter WIDTH = 16,
    parameter NUM   = 4
) (
    input  logic                         clk,
    input  logic [WIDTH-1:0]             in_bus [NUM],
    output logic [WIDTH-1:0]             out_bus [NUM]
);
    genvar i;
    generate
        for (i = 0; i < NUM; i++) begin : gen_block
            always_ff @(posedge clk) begin
                out_bus[i] <= in_bus[i];
            end
        end
    endgenerate
endmodule
module stat_union (
    input  logic        clk,
    input  logic [31:0] in_word,
    output logic [15:0] out_half
);
    typedef union packed {
        logic [31:0] word;
        struct packed {
            logic [15:0] low;
            logic [15:0] high;
        } halves;
    } word_u;
    word_u data_u;
    always_ff @(posedge clk) begin
        data_u.word <= in_word;
    end
    assign out_half = data_u.halves.low;
endmodule
module stat_assert (
    input  logic        clk,
    input  logic [7:0]  in_value,
    output logic [7:0]  out_value
);
    always_comb begin
        out_value = in_value;
        assert (in_value != 8'hFF) else out_value = 8'h00;
        if (!clk) out_value = 8'hAA;
    end
endmodule
module stat_cover (
    input  logic clk,
    input  logic sig,
    output logic cov_out
);
    always_ff @(posedge clk) begin
        cov_out <= sig;
        cover (sig);
    end
endmodule
