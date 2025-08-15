import "DPI-C" function int c_add(input int a, input int b);
class MyClass;
    int x;
    function new(int v);
        x = v;
    endfunction
    function int get();
        return x;
    endfunction
endclass
module attr_test
  #(parameter int WIDTH = 8)
  (input  logic               clk,
   input  logic [WIDTH-1:0]   in_data,
   output logic [WIDTH-1:0]   out_data);
    typedef enum logic [1:0] {
        IDLE = 2'b00,
        RUN  = 2'b01,
        HOLD = 2'b10,
        DONE = 2'b11
    } state_t;
    state_t state;
    always_ff @(posedge clk) begin
        state <= (in_data == '0) ? IDLE : RUN;
        if (state == RUN) out_data <= in_data;
        else out_data <= '0;
    end
endmodule
module gen_logic
  #(parameter int N = 4)
  (input  logic [N-1:0] in_v,
   output logic [N-1:0] out_v);
    generate
        genvar i;
        for (i = 0; i < N; i++) begin : gen_block
            localparam logic LSB = (i % 2);
            assign out_v[i] = in_v[i] ^ LSB;
        end
    endgenerate
endmodule
module union_demo
  (input  logic [31:0] in_word,
   output logic [7:0]  byte3);
    typedef union packed {
        logic [31:0]        word;
        logic [3:0][7:0]    bytes;
    } word_u;
    word_u u;
    always_comb begin
        u.word = in_word;
        byte3  = u.bytes[3];
    end
endmodule
module struct_demo
  (input  logic [15:0] a,
   input  logic [15:0] b,
   output logic [31:0] sum);
    typedef struct packed {
        logic [15:0] lo;
        logic [15:0] hi;
    } pairs_s;
    pairs_s s_in;
    always_comb begin
        s_in.lo = a;
        s_in.hi = b;
        sum     = {s_in.hi, s_in.lo};
    end
endmodule
module dpi_demo
  (input  logic [31:0] in0,
   input  logic [31:0] in1,
   output logic [31:0] add_out);
    int result;
    always_comb begin
        result  = c_add(int'(in0), int'(in1));
        add_out = result;
    end
endmodule
module class_demo
  (input  logic [31:0] val_in,
   output logic [31:0] val_out);
    always_comb begin
        MyClass obj = new(int'(val_in));
        val_out = obj.get();
    end
endmodule
module assert_demo
  (input  logic clk,
   input  logic rst,
   input  logic din,
   output logic dout);
    always_ff @(posedge clk) begin
        if (rst) dout <= 1'b0;
        else     dout <= din;
    end
    property stable_input;
        @(posedge clk) disable iff (rst) $stable(din);
    endproperty
    assert property (stable_input);
    cover  property (stable_input);
endmodule
module func_demo
  (input  logic [7:0] in_a,
   output logic [7:0] out_a);
    function automatic logic [7:0] reverse_bits(input logic [7:0] data);
        reverse_bits = {data[0], data[1], data[2], data[3],
                        data[4], data[5], data[6], data[7]};
    endfunction
    always_comb out_a = reverse_bits(in_a);
endmodule
module unique_case_demo
  (input  logic [1:0] sel,
   output logic       out_flag);
    always_comb begin
        unique case (sel)
            2'b00: out_flag = 1'b0;
            2'b01: out_flag = 1'b1;
            2'b10,
            2'b11: out_flag = 1'b1;
        endcase
    end
endmodule
module priority_if_demo
  (input  logic [3:0] in_d,
   output logic [1:0] pos);
    always_comb begin
        priority if (in_d[0]) pos = 2'd0;
        else if (in_d[1])     pos = 2'd1;
        else if (in_d[2])     pos = 2'd2;
        else if (in_d[3])     pos = 2'd3;
        else                  pos = 2'd0;
    end
endmodule
