package util_pkg;
  typedef struct packed {
    logic [7:0]  id;
    logic [31:0] data;
  } packet_t;
endpackage
interface simple_if #(parameter WIDTH = 8) ();
  logic [WIDTH-1:0] data;
  modport consumer (input  data);
  modport producer (output data);
endinterface
module arithmetic_unit (
    input  logic [31:0] a,
    input  logic [31:0] b,
    input  logic        sel,
    output logic [31:0] y
);
    always_comb begin
        unique case (sel)
            1'b0 : y = a + b;
            1'b1 : y = a - b;
            default: y = 'x;
        endcase
    end
endmodule
module shift_rotate (
    input  logic [31:0] data,
    input  logic [1:0]  mode,
    output logic [31:0] result
);
    always_comb begin
        priority case (mode)
            2'b00: result = data << 1;
            2'b01: result = data >> 1;
            2'b10: result = {data[0],  data[31:1]};
            2'b11: result = {data[30:0], data[31]};
        endcase
    end
endmodule
module class_example (
    input  logic [7:0] in_value,
    output logic [7:0] out_value
);
    class incrementer;
        function automatic [7:0] do_inc(input [7:0] v);
            return v + 1;
        endfunction
    endclass
    always_comb begin
        automatic incrementer inc = new();
        out_value = inc.do_inc(in_value);
    end
endmodule
module pipeline_stage (
    input  util_pkg::packet_t  in_pkt,
    output util_pkg::packet_t  out_pkt
);
    always_comb begin
        out_pkt       = in_pkt;
        out_pkt.data  = in_pkt.data + 1;
    end
endmodule
module coverage_example (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [3:0]  sig_in,
    output logic        sampled
);
    typedef enum logic [1:0] {IDLE, ACTIVE, ERROR} state_t;
    state_t state;
    covergroup cg @(posedge clk);
        option.auto_bin_max = 4;
        coverpoint sig_in;
    endgroup
    cg cg_inst = new();
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state   <= IDLE;
            sampled <= 1'b0;
        end else begin
            state   <= ACTIVE;
            sampled <= sig_in[0];
            cg_inst.sample();
        end
    end
endmodule
module array_ops (
    input  logic [3:0] idx,
    output logic [7:0] value
);
    logic [7:0] data_array [10];
    always_comb begin
        foreach (data_array[i]) data_array[i] = i[7:0];
        if (idx < 10)
            value = data_array[idx];
        else
            value = 8'h00;
    end
endmodule
module union_example (
    input  logic [31:0] in_word,
    output logic [3:0]  nibble0
);
    typedef union packed {
        logic [31:0]       word;
        logic [3:0][7:0]   bytes;
    } word_union_t;
    always_comb begin
        word_union_t u;
        u.word  = in_word;
        nibble0 = u.bytes[0][3:0];
    end
endmodule
module param_logic #(
    parameter WIDTH = 8
) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH-1:0] y
);
    generate
        if (WIDTH <= 8) begin
            always_comb begin
                y = a ^ b;
            end
        end else begin
            always_comb begin
                y = a ~^ b;
            end
        end
    endgenerate
endmodule
module if_consumer (
    input  logic clk,
    output logic [7:0] out_data
);
    simple_if #(.WIDTH(8)) intf();
    always_comb begin
        out_data = intf.data;
    end
endmodule
