package design_types;
    typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;
endpackage
interface simple_if #(parameter WIDTH = 8) (input logic clk);
    logic [WIDTH-1:0] data_in;
    logic [WIDTH-1:0] data_out;
    modport producer (output data_in, input  clk);
    modport consumer (input  data_in, output data_out, input clk);
endinterface
module adder_comb #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in_a,
    input  logic [WIDTH-1:0] in_b,
    output logic [WIDTH   :0] sum
);
    always_comb sum = in_a + in_b;
endmodule
module state_machine (
    input  logic clk,
    input  logic rst_n,
    input  logic start,
    output logic done
);
    import design_types::*;
    state_t state, next;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) state <= IDLE;
        else        state <= next;
    always_comb begin
        next = state;
        done = 1'b0;
        case (state)
            IDLE: if (start) next = RUN;
            RUN :           next = DONE;
            DONE: begin
                      done = 1'b1;
                      if (!start) next = IDLE;
                  end
        endcase
    end
endmodule
module interface_user #(parameter WIDTH = 8) (
    input  logic                 clk,
    input  logic [WIDTH-1:0]     ext_in,
    output logic [WIDTH-1:0]     ext_out,
    output logic                 flag
);
    simple_if #(.WIDTH(WIDTH)) bus(clk);
    assign bus.data_in = ext_in;
    always_ff @(posedge clk)
        bus.data_out <= bus.data_in + 1;
    assign ext_out = bus.data_out;
    assign flag    = ^bus.data_out;
endmodule
module fifo_model #(parameter DEPTH = 4, parameter WIDTH = 8) (
    input  logic                  clk,
    input  logic                  rst_n,
    input  logic                  write_en,
    input  logic                  read_en,
    input  logic [WIDTH-1:0]      data_in,
    output logic [WIDTH-1:0]      data_out,
    output logic                  full,
    output logic                  empty
);
    logic [WIDTH-1:0] mem [DEPTH-1:0];
    int wr_ptr, rd_ptr, count;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr   <= 0;
            rd_ptr   <= 0;
            count    <= 0;
            data_out <= '0;
        end else begin
            if (write_en && !full) begin
                mem[wr_ptr] <= data_in;
                wr_ptr      <= (wr_ptr + 1) % DEPTH;
                count       <= count + 1;
            end
            if (read_en && !empty) begin
                data_out <= mem[rd_ptr];
                rd_ptr   <= (rd_ptr + 1) % DEPTH;
                count    <= count - 1;
            end
        end
    end
    assign full  = (count == DEPTH);
    assign empty = (count == 0);
endmodule
module bitfield_packer (
    input  logic [15:0] in_word,
    output logic [7:0]  out_high,
    output logic [7:0]  out_low
);
    typedef union packed {
        logic [15:0] word;
        struct packed {
            logic [7:0] low;
            logic [7:0] high;
        } bytes;
    } word_u;
    word_u u;
    always_comb begin
        u.word   = in_word;
        out_high = u.bytes.high;
        out_low  = u.bytes.low;
    end
endmodule
module class_example (
    input  logic       tr,
    output logic [31:0] result
);
    class multiplier;
        function automatic int mult (int a, int b);
            return a * b;
        endfunction
    endclass
    multiplier m;
    always_comb begin
        if (tr && m != null) result = m.mult(3, 4);
        else                 result = 32'd0;
    end
    initial m = new();
endmodule
module generate_example #(parameter WIDTH = 4) (
    input  logic [WIDTH-1:0] in_vec,
    output logic [WIDTH-1:0] out_vec
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_blk
            assign out_vec[i] = ~in_vec[i];
        end
    endgenerate
endmodule
module function_task_example (
    input  logic       clk,
    input  logic [7:0] value_in,
    output logic [7:0] value_out
);
    function automatic logic [7:0] reverse_bits (input logic [7:0] v);
        logic [7:0] r;
        int i;
        begin
            for (i = 0; i < 8; i++) r[i] = v[7-i];
            return r;
        end
    endfunction
    task automatic compute;
        value_out <= reverse_bits(value_in);
    endtask
    always_ff @(posedge clk) compute();
endmodule
module signed_arith (
    input  logic signed [7:0] in_x,
    input  logic signed [7:0] in_y,
    output logic signed [8:0] diff
);
    assign diff = in_x - in_y;
endmodule
module array_reduce_example (
    input  logic [15:0] vec,
    output logic        parity
);
    assign parity = ^vec;
endmodule
