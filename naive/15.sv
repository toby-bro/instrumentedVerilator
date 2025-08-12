package my_pkg;
   typedef enum logic [1:0] {IDLE=2'd0, RUN=2'd1, DONE=2'd2} state_e;
   typedef struct packed {
       logic [15:0] data;
       logic        valid;
   } packet_t;
   class helper;
       function automatic int increment (int x);
           return x + 1;
       endfunction
   endclass
endpackage
module enum_struct_module #(
    parameter WIDTH = 16
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic [WIDTH-1:0]        in_data,
    output logic [WIDTH-1:0]        out_data
);
    import my_pkg::*;
    state_e   state;
    packet_t  packet_reg;
    helper    h;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state             <= IDLE;
            packet_reg        <= '0;
            out_data          <= '0;
            h = new();
        end else begin
            case (state)
                IDLE: begin
                    packet_reg.data  <= in_data;
                    packet_reg.valid <= 1'b1;
                    state            <= RUN;
                end
                RUN: begin
                    if (packet_reg.valid) begin
                        out_data      <= packet_reg.data;
                        state         <= DONE;
                    end
                end
                DONE: begin
                    out_data          <= '0;
                    state             <= IDLE;
                end
            endcase
        end
    end
endmodule
module array_types_module (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [7:0]  in_byte,
    output logic [15:0] out_sum
);
    int unsigned           dyn[];
    int                    assoc[string];
    byte                   queue_byte[$];
    class accumulator;
        int total;
        function void add (int v);
            total += v;
        endfunction
        function int get ();
            return total;
        endfunction
    endclass
    accumulator acc;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            dyn         = new[0];
            queue_byte  = {};
            assoc.delete();
            out_sum     <= 16'd0;
            acc         = new();
        end else begin
            if (dyn.size() == 0) begin
                dyn = new[1];
                dyn[0] = in_byte;
            end else begin
                dyn = new[dyn.size()+1](dyn);
                dyn[dyn.size()-1] = in_byte;
            end
            queue_byte.push_back(in_byte);
            assoc["last"] = int'(in_byte);
            acc.add(int'(in_byte));
            out_sum <= acc.get();
        end
    end
endmodule
module union_packed_module (
    input  logic [31:0] in_word,
    output logic [7:0]  out_byte0,
    output logic [7:0]  out_byte1,
    output logic [7:0]  out_byte2,
    output logic [7:0]  out_byte3
);
    typedef struct packed {
        logic [7:0] b0;
        logic [7:0] b1;
        logic [7:0] b2;
        logic [7:0] b3;
    } bytes_t;
    typedef union packed {
        logic  [31:0] word;
        bytes_t       bytes;
    } word_bytes_u;
    word_bytes_u u;
    always_comb begin
        u.word    = in_word;
        out_byte0 = u.bytes.b0;
        out_byte1 = u.bytes.b1;
        out_byte2 = u.bytes.b2;
        out_byte3 = u.bytes.b3;
    end
endmodule
module property_assert_module (
    input  logic clk,
    input  logic rst_n,
    input  logic req,
    input  logic gnt,
    output logic busy
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            busy <= 1'b0;
        end else begin
            if (req  && !busy) busy <= 1'b1;
            if (busy &&  gnt)  busy <= 1'b0;
        end
    end
    property req_to_busy;
        @(posedge clk) disable iff (!rst_n)
            req |-> ##1 busy;
    endproperty
    assert property (req_to_busy);
endmodule
module generate_example #(
    parameter N = 4
) (
    input  logic [N-1:0] in_vec,
    output logic [N-1:0] out_vec
);
    genvar i;
    for (i = 0; i < N; i++) begin : bit_reversal
        assign out_vec[i] = in_vec[N-1-i];
    end
endmodule
