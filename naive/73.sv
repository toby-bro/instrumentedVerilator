interface simple_if(input logic clk, input logic rst);
    logic valid;
    logic [7:0] data;
endinterface
module simple_assign(input logic [7:0] in, output logic [7:0] out);
    assign out = in;
endmodule
module always_class(input logic clk, input logic rst, output logic [31:0] data_out);
    class packet;
        rand logic [31:0] payload;
        function new(); payload = 0; endfunction
        function void gen(); payload = payload + 1; endfunction
    endclass
    packet pkt;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            pkt = new();
            data_out <= 0;
        end else begin
            pkt.gen();
            data_out <= pkt.payload;
        end
    end
endmodule
module param_gen #(parameter int N = 8) (input logic [N-1:0] in, output logic [N-1:0] out);
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : gen_bits
            assign out[i] = ~in[i];
        end
    endgenerate
endmodule
module function_struct(input logic [15:0] in, output logic [15:0] out);
    typedef struct packed { logic [7:0] hi; logic [7:0] lo; } half_word_t;
    function half_word_t swap_bytes(half_word_t x);
        half_word_t tmp;
        begin
            tmp.hi = x.lo;
            tmp.lo = x.hi;
            swap_bytes = tmp;
        end
    endfunction
    half_word_t hw;
    always_comb begin
        hw.hi = in[15:8];
        hw.lo = in[7:0];
        hw = swap_bytes(hw);
        out = {hw.hi, hw.lo};
    end
endmodule
module task_union_enum(input logic a, input logic b, output logic result);
    typedef enum logic [1:0] {IDLE = 2'b00, BUSY = 2'b01, DONE = 2'b10} state_t;
    typedef union packed { logic [1:0] as_bits; state_t as_state; } u_t;
    state_t curr;
    u_t u_in, u_out;
    task compute(input u_t in_val, output u_t out_val);
        begin
            out_val.as_bits = in_val.as_bits + 2'b01;
        end
    endtask
    always_comb begin
        curr = IDLE;
        u_in.as_state = curr;
        compute(u_in, u_out);
        result = (u_out.as_state != IDLE);
    end
endmodule
module if_mod(input logic clk, input logic rst, input logic en, output logic ready);
    simple_if intf(.clk(clk), .rst(rst));
    assign intf.valid = en;
    logic [3:0] counter;
    always_ff @(posedge intf.clk or posedge intf.rst) begin
        if (intf.rst) counter <= 0;
        else if (intf.valid && en) counter <= counter + 1;
    end
    assign ready = (counter == 4'd10);
endmodule
module queue_class(input logic clk, input logic rst, input logic wr_en, input logic rd_en, input logic [7:0] din, output logic [7:0] dout, output logic full, output logic empty);
    localparam int DEPTH = 4;
    class fifo;
        logic [7:0] mem [DEPTH];
        int head, tail, count;
        function new(); head = 0; tail = 0; count = 0; endfunction
        function void push(logic [7:0] d);
            if (count < DEPTH) begin
                mem[tail] = d;
                tail = (tail + 1) % DEPTH;
                count = count + 1;
            end
        endfunction
        function logic [7:0] pop();
            logic [7:0] tmp;
            if (count > 0) begin
                tmp = mem[head];
                head = (head + 1) % DEPTH;
                count = count - 1;
            end else begin
                tmp = '0;
            end
            return tmp;
        endfunction
    endclass
    fifo q;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) q = new();
        else begin
            if (wr_en) q.push(din);
            if (rd_en) dout <= q.pop();
        end
    end
    always_comb begin
        full = (q.count == DEPTH);
        empty = (q.count == 0);
    end
endmodule
