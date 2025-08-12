interface bus_if #(parameter WIDTH = 8) (input logic clk);
    logic [WIDTH-1:0] data;
    logic             valid;
    logic             ready;
    modport master (output data, output valid, input ready);
    modport slave  (input  data, input  valid, output ready);
endinterface
module bitwise_ops (
    input  logic [7:0] in_data,
    output logic [7:0] out_rot,
    output logic       parity
);
    always_comb begin
        out_rot = {in_data[0], in_data[7:1]};
        parity  = ^in_data;
    end
endmodule
module struct_union_mod (
    input  logic [31:0] in_word,
    output logic [7:0]  byte_sum
);
    typedef struct packed {
        logic [7:0] byte0;
        logic [7:0] byte1;
        logic [7:0] byte2;
        logic [7:0] byte3;
    } byte_struct_t;
    byte_struct_t bs;
    always_comb begin
        bs       = in_word;
        byte_sum = bs.byte0 + bs.byte1 + bs.byte2 + bs.byte3;
    end
endmodule
module enum_fsm (
    input  logic clk,
    input  logic rst,
    input  logic start,
    output logic done
);
    typedef enum logic [1:0] {IDLE=2'd0, BUSY=2'd1, FINISHED=2'd2} state_t;
    state_t state, next_state;
    always_comb begin
        next_state = state;
        done       = 1'b0;
        case (state)
            IDLE:     if (start)         next_state = BUSY;
            BUSY:                          next_state = FINISHED;
            FINISHED: begin
                done = 1'b1;
                if (!start)              next_state = IDLE;
            end
            default:                      next_state = IDLE;
        endcase
    end
    always_ff @(posedge clk or posedge rst) begin
        if (rst)  state <= IDLE;
        else      state <= next_state;
    end
endmodule
module if_master #(parameter WIDTH = 8) (
    input  logic        clk,
    input  logic        rst_n,
    output logic        busy
);
    bus_if #(WIDTH) m_if(clk);
    typedef enum logic [1:0] {S_IDLE=2'd0, S_SEND=2'd1, S_WAIT=2'd2} mstate_t;
    mstate_t            state, next_state;
    logic [WIDTH-1:0]   counter;
    always_comb begin
        next_state  = state;
        m_if.valid  = 1'b0;
        m_if.data   = counter;
        busy        = 1'b0;
        case (state)
            S_IDLE: begin
                busy = 1'b0;
                if (counter != '0)      next_state = S_SEND;
            end
            S_SEND: begin
                m_if.valid = 1'b1;
                busy       = 1'b1;
                next_state = S_WAIT;
            end
            S_WAIT: begin
                busy = 1'b1;
                next_state = S_IDLE;
            end
            default:                    next_state = S_IDLE;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state   <= S_IDLE;
            counter <= '0;
        end else begin
            state   <= next_state;
            counter <= counter + 1'b1;
        end
    end
endmodule
module class_demo (
    input  logic [3:0] a,
    output logic [3:0] b
);
    class adder_c;
        function automatic logic [3:0] plus1 (input logic [3:0] x);
            plus1 = x + 1'b1;
        endfunction
    endclass
    always_comb begin
        adder_c ad;
        ad = new();
        b  = ad.plus1(a);
    end
endmodule
module cover_example (
    input  logic       clk,
    input  logic [7:0] data_in,
    output logic       flag
);
    covergroup cg @(posedge clk);
        coverpoint data_in;
    endgroup
    cg cgi = new();
    always_ff @(posedge clk) begin
        cgi.sample();
        flag <= data_in[0];
    end
endmodule
module gen_loop #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in_bus,
    output logic [WIDTH-1:0] out_bus
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : bit_inv
            assign out_bus[i] = ~in_bus[i];
        end
    endgenerate
endmodule
