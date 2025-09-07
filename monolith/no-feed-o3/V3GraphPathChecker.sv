//============================================================
module comb_seq_graph (
    input  logic         clk,
    input  logic  [15:0] in_bus,
    output logic  [15:0] out_bus
);
    logic [15:0] stage1, stage2, stage3, stage4;
    always_comb begin
        stage1 = {in_bus[7:0], in_bus[15:8]} + 16'h1F1F;
    end
    always_ff @(posedge clk) begin
        stage2 <= stage1 ^ 16'hAAAA;
    end
    always_comb begin
        stage3 = stage2 + stage1;
        stage4 = (stage3 & 16'h0F0F) | (stage2 & 16'hF0F0);
    end
    assign out_bus = stage4;
endmodule
//============================================================
module generate_graph #(
    parameter WIDTH = 8
) (
    input  logic                  clk,
    input  logic [WIDTH-1:0]      in_vec,
    output logic [WIDTH-1:0]      out_vec
);
    logic [WIDTH-1:0] temp_vec;
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_blk
            always_ff @(posedge clk) begin
                temp_vec[i] <= in_vec[i] ^ temp_vec[(i+1) % WIDTH];
            end
        end
    endgenerate
    assign out_vec = temp_vec;
endmodule
//============================================================
module aggregate_graph (
    input  logic        clk,
    input  logic [7:0]  din,
    output logic [7:0]  dout
);
    typedef struct packed {
        logic [3:0] lo;
        logic [3:0] hi;
    } nib_struct_t;
    typedef union packed {
        nib_struct_t s;
        logic [7:0]  vec;
    } data_u;
    data_u reg_u, next_u;
    always_comb begin
        next_u.vec        = din + 8'h55;
        next_u.s.hi       = next_u.s.hi ^ next_u.s.lo;
    end
    always_ff @(posedge clk) begin
        reg_u <= next_u;
    end
    assign dout = reg_u.vec;
endmodule
//============================================================
module class_graph (
    input  logic clk,
    input  logic [3:0]  in_val,
    output logic [3:0]  out_val
);
    class adder_c;
        function logic [3:0] add4(logic [3:0] a);
            return a + 4'd4;
        endfunction
    endclass
    adder_c adder_h;
    always_ff @(posedge clk) begin
        adder_h = new();
        out_val <= adder_h.add4(in_val);
    end
endmodule
//============================================================
module func_task_graph (
    input  logic        clk,
    input  logic [11:0] in_data,
    output logic [11:0] out_data
);
    function automatic logic [11:0] reverse_bits (input logic [11:0] dat);
        logic [11:0] r;
        integer k;
        for (k = 0; k < 12; k++) begin
            r[k] = dat[11-k];
        end
        return r;
    endfunction
    task automatic mix_bits (
        input  logic [11:0] src,
        output logic [11:0] dst
    );
        dst = (src << 3) | (src >> 9);
    endtask
    logic [11:0] temp1, temp2;
    always_ff @(posedge clk) begin
        temp1  <= reverse_bits(in_data);
        mix_bits(temp1, temp2);
        out_data <= temp2 ^ temp1;
    end
endmodule
//============================================================
module param_graph #(
    parameter int SIZE = 6
) (
    input  logic                clk,
    input  logic signed [SIZE:0] a,
    input  logic signed [SIZE:0] b,
    output logic signed [SIZE:0] y
);
    logic signed [SIZE:0] sum, diff;
    always_comb begin
        sum  = a + b;
        diff = a - b;
    end
    always_ff @(posedge clk) begin
        y <= (a[SIZE] == b[SIZE]) ? sum : diff;
    end
endmodule
//============================================================
module array_graph (
    input  logic             clk,
    input  logic  [3:0][7:0] in_mat,
    output logic [3:0][7:0]  out_mat
);
    logic [3:0][7:0] reg_mat;
    integer idx, jdx;
    always_ff @(posedge clk) begin
        for (idx = 0; idx < 4; idx++) begin
            for (jdx = 0; jdx < 8; jdx++) begin
                reg_mat[idx][jdx] <= in_mat[idx][jdx] ^ reg_mat[(idx+1)%4][(jdx+2)%8];
            end
        end
    end
    assign out_mat = reg_mat;
endmodule
//============================================================
module slice_graph (
    input  logic        clk,
    input  logic [31:0] din,
    output logic [31:0] dout
);
    logic [31:0]      r1;
    logic [15:0]      upper, lower;
    logic [31:0]      merged;
    always_ff @(posedge clk) begin
        r1 <= {din[15:0], din[31:16]};
    end
    always_comb begin
        upper      = r1[31:16] + 16'h1234;
        lower      = r1[15:0]  ^ 16'h5678;
        merged     = {upper, lower};
    end
    assign dout = merged;
endmodule
