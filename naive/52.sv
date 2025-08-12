module param_adder #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH-1:0] sum
);
    assign sum = a + b;
endmodule
module func_module (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [7:0]  in,
    output logic [7:0]  out
);
    function automatic logic [7:0] reverse_bits(input logic [7:0] val);
        for (int i = 0; i < 8; i++) begin
            reverse_bits[i] = val[7-i];
        end
    endfunction
    always_comb begin
        out = reverse_bits(in);
    end
endmodule
module task_module (
    input  logic [3:0] in,
    output logic [7:0] out
);
    task automatic multiply_by_two(input logic [3:0] in_val, output logic [7:0] out_val);
        out_val = in_val * 2;
    endtask
    always_comb begin
        multiply_by_two(in, out);
    end
endmodule
module generate_module #(parameter N = 4) (
    input  logic [N-1:0] in,
    output logic [N-1:0] out
);
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : gen_bits
            assign out[i] = ~in[i];
        end
    endgenerate
endmodule
module case_module (
    input  logic [1:0]  sel,
    input  logic [7:0]  data0,
    input  logic [7:0]  data1,
    input  logic [7:0]  data2,
    input  logic [7:0]  data3,
    output logic [7:0]  out
);
    always_comb begin
        case (sel)
            2'b00: out = data0;
            2'b01: out = data1;
            2'b10: out = data2;
            default: out = data3;
        endcase
    end
endmodule
module class_module (
    input  logic        clk,
    input  logic        rst,
    input  logic [3:0]  in,
    output logic [3:0]  out
);
    class regfile;
        rand logic [3:0] memory;
        function void write(input logic [3:0] val);
            memory = val;
        endfunction
        function logic [3:0] read();
            return memory;
        endfunction
    endclass
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            out <= '0;
        end else begin
            regfile rf = new();
            rf.write(in);
            out <= rf.read();
        end
    end
endmodule
module fifo #(parameter DEPTH = 8, parameter WIDTH = 8) (
    input  logic                  clk,
    input  logic                  rst,
    input  logic                  wr_en,
    input  logic                  rd_en,
    input  logic [WIDTH-1:0]      wr_data,
    output logic [WIDTH-1:0]      rd_data
);
    logic [WIDTH-1:0] mem [0:DEPTH-1];
    logic [$clog2(DEPTH):0] wr_ptr, rd_ptr;
    logic full, empty;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            wr_ptr <= 0;
            rd_ptr <= 0;
        end else begin
            if (wr_en && !full) begin
                mem[wr_ptr] <= wr_data;
                wr_ptr <= wr_ptr + 1;
            end
            if (rd_en && !empty) begin
                rd_data <= mem[rd_ptr];
                rd_ptr <= rd_ptr + 1;
            end
        end
    end
    assign full  = (wr_ptr == DEPTH);
    assign empty = (wr_ptr == rd_ptr);
endmodule
