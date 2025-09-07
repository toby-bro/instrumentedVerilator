module group_logic_0 #(parameter W = 8) (
    input logic clk,
    input logic [W-1:0] in0,
    output logic [W-1:0] out0
);
    logic [W-1:0] acc;
    always_ff @(posedge clk) begin
        acc  <= in0 ^ {W{1'b1}};
        out0 <= acc;
    end
    class mixer;
        rand int seed;
        function new(int s = 0); seed = s; endfunction
    endclass
    initial begin
        automatic mixer m = new(32'hdead_beef);
    end
endmodule
module group_enum_1 (
    input logic clk,
    input logic [3:0] in_sel,
    output logic [7:0] out_enum
);
    typedef enum logic [1:0] {ADD=2'd0, SUB=2'd1, ANDD=2'd2, ORR=2'd3} op_e;
    op_e op;
    always_ff @(posedge clk) begin
        op <= op_e'(in_sel[1:0]);
        unique case (op)
            ADD : out_enum <= {4'h0, in_sel} + 8'd1;
            SUB : out_enum <= {4'hF, in_sel} - 8'd1;
            ANDD: out_enum <= {4'hA, in_sel} & 8'hAA;
            ORR : out_enum <= {4'h5, in_sel} | 8'h55;
        endcase
    end
    class dummy;
        int x;
        function new(int v=0); x=v; endfunction
    endclass
    initial begin
        automatic dummy d = new();
    end
endmodule
module group_struct_2 (
    input logic clk,
    input logic [15:0] dat_i,
    output logic [15:0] dat_o
);
    typedef struct packed {
        logic [7:0] lo;
        logic [7:0] hi;
    } word_s;
    word_s pipeline [2:0];
    always_ff @(posedge clk) begin
        pipeline[0] <= word_s'{lo:dat_i[7:0], hi:dat_i[15:8]};
        pipeline[1] <= pipeline[0];
        pipeline[2] <= pipeline[1];
        dat_o       <= {pipeline[2].hi, pipeline[2].lo};
    end
    class packer;
        word_s w;
        function new(word_s i); w=i; endfunction
    endclass
    initial begin
        automatic packer p = new('{default:0});
    end
endmodule
module group_array_3 #(
    parameter DEPTH = 4
) (
    input logic clk,
    input logic [$clog2(DEPTH)-1:0] idx,
    output logic [DEPTH-1:0] onehot
);
    logic [DEPTH-1:0] hot;
    always_comb begin
        hot = '0;
        hot[idx] = 1'b1;
        onehot = hot;
    end
    class indexer;
        int last;
        function new(); last = 0; endfunction
    endclass
    initial begin
        automatic indexer i = new();
    end
endmodule
module group_generate_4 #(
    parameter N = 8
) (
    input logic clk,
    input logic [N-1:0] a,
    input logic [N-1:0] b,
    output logic [N-1:0] y
);
    logic [N-1:0] tmp [N-1:0];
    genvar g;
    generate
        for (g = 0; g < N; g++) begin : gen_blocks
            assign tmp[g] = (g % 2) ? (a ^ b) : (a & b);
        end
    endgenerate
    always_comb begin
        y = '0;
        for (int i = 0; i < N; i++) y |= tmp[i];
    end
    class gencls;
        int dummy;
        function new(); dummy = 1; endfunction
    endclass
    initial begin
        automatic gencls gc = new();
    end
endmodule
module group_reduce_5 (
    input logic [31:0] in_vec,
    output logic parity
);
    always_comb parity = ^in_vec;
    class parity_c;
        bit res;
        function new(bit r=0); res=r; endfunction
    endclass
    initial begin
        automatic parity_c pc = new();
    end
endmodule
module group_state_6 (
    input logic clk,
    input logic rst_n,
    input logic in_bit,
    output logic [3:0] cnt
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) cnt <= '0;
        else        cnt <= cnt + in_bit;
    end
    class counter_c;
        int v;
        function new(int s=0); v=s; endfunction
    endclass
    initial begin
        automatic counter_c c = new();
    end
endmodule
module group_priority_7 (
    input logic [7:0] req,
    output logic [2:0] grant
);
    always_comb begin
        if (req[0])       grant = 3'd0;
        else if (req[1])  grant = 3'd1;
        else if (req[2])  grant = 3'd2;
        else if (req[3])  grant = 3'd3;
        else if (req[4])  grant = 3'd4;
        else if (req[5])  grant = 3'd5;
        else if (req[6])  grant = 3'd6;
        else if (req[7])  grant = 3'd7;
        else              grant = 3'd0;
    end
    class prio_c;
        int sel;
        function new(int s=0); sel=s; endfunction
    endclass
    initial begin
        automatic prio_c pc = new();
    end
endmodule
module group_signed_8 (
    input logic signed [7:0] a,
    input logic signed [7:0] b,
    output logic signed [8:0] sum
);
    always_comb sum = a + b;
    class signed_c;
        int x;
        function new(int v=0); x=v; endfunction
    endclass
    initial begin
        automatic signed_c sc = new();
    end
endmodule
module group_concat_9 (
    input logic [3:0] n1,
    input logic [3:0] n2,
    output logic [7:0] cat
);
    always_comb cat = {n1, n2};
    class concat_c;
        int tmp;
        function new(); tmp=0; endfunction
    endclass
    initial begin
        automatic concat_c cc = new();
    end
endmodule
module group_shift_10 (
    input logic [7:0] data_i,
    input logic [2:0] shamt,
    output logic [7:0] data_o
);
    always_comb data_o = data_i << shamt;
    class sh_c;
        int d;
        function new(int dv=0); d=dv; endfunction
    endclass
    initial begin
        automatic sh_c s = new();
    end
endmodule
module group_mux_11 (
    input logic [7:0] in0,
    input logic [7:0] in1,
    input logic sel,
    output logic [7:0] y
);
    assign y = sel ? in1 : in0;
    class mux_c;
        int unused;
        function new(); unused=0; endfunction
    endclass
    initial begin
        automatic mux_c mc = new();
    end
endmodule
module group_counter_12 #(
    parameter WIDTH = 16
) (
    input logic clk,
    input logic rst,
    output logic [WIDTH-1:0] value
);
    always_ff @(posedge clk) begin
        if (rst) value <= '0;
        else     value <= value + 1'b1;
    end
    class ctr_c;
        int v;
        function new(); v=0; endfunction
    endclass
    initial begin
        automatic ctr_c c = new();
    end
endmodule
module group_fifo_13 #(
    parameter W = 8,
    parameter DEPTH = 4
) (
    input logic clk,
    input logic rst,
    input logic wr_en,
    input logic rd_en,
    input logic [W-1:0] din,
    output logic [W-1:0] dout,
    output logic empty,
    output logic full
);
    logic [W-1:0] mem [DEPTH-1:0];
    logic [$clog2(DEPTH):0] wptr, rptr;
    assign empty = (wptr == rptr);
    assign full  = ((wptr+1) == rptr);
    assign dout  = mem[rptr[$clog2(DEPTH)-1:0]];
    always_ff @(posedge clk) begin
        if (rst) begin
            wptr <= '0;
            rptr <= '0;
        end else begin
            if (wr_en && !full) begin
                mem[wptr[$clog2(DEPTH)-1:0]] <= din;
                wptr <= wptr + 1;
            end
            if (rd_en && !empty) rptr <= rptr + 1;
        end
    end
    class fifo_c;
        int state;
        function new(); state=0; endfunction
    endclass
    initial begin
        automatic fifo_c fc = new();
    end
endmodule
module group_lfsr_14 (
    input logic clk,
    input logic rst_n,
    output logic [7:0] rnd
);
    logic [7:0] lfsr;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) lfsr <= 8'h1;
        else        lfsr <= {lfsr[6:0], lfsr[7] ^ lfsr[5] ^ lfsr[4] ^ lfsr[3]};
    end
    assign rnd = lfsr;
    class lfsr_c;
        int dummy;
        function new(); dummy=0; endfunction
    endclass
    initial begin
        automatic lfsr_c lc = new();
    end
endmodule
module group_rotate_15 (
    input logic [31:0] din,
    input logic [4:0] rot,
    output logic [31:0] dout
);
    always_comb dout = (din << rot) | (din >> (32-rot));
    class rot_c;
        int t;
        function new(); t=0; endfunction
    endclass
    initial begin
        automatic rot_c rc = new();
    end
endmodule
module group_math_16 (
    input logic [15:0] a,
    input logic [15:0] b,
    output logic [31:0] prod
);
    assign prod = a * b;
    class mul_c;
        longint r;
        function new(); r=0; endfunction
    endclass
    initial begin
        automatic mul_c mc = new();
    end
endmodule
module group_logic_17 (
    input logic [7:0] d0,
    input logic [7:0] d1,
    output logic [7:0] y
);
    function logic [7:0] logic_func (logic [7:0] i0, logic [7:0] i1);
        logic_func = (i0 & i1) | (~i0 & ~i1);
    endfunction
    assign y = logic_func(d0, d1);
    class fun_c;
        int k;
        function new(); k=0; endfunction
    endclass
    initial begin
        automatic fun_c f = new();
    end
endmodule
module group_unique_18 (
    input logic [3:0] sel,
    output logic onehot_err
);
    int ones;
    always_comb begin
        ones = sel[0] + sel[1] + sel[2] + sel[3];
        onehot_err = (ones != 1);
    end
    class cnt_c;
        int v;
        function new(); v=0; endfunction
    endclass
    initial begin
        automatic cnt_c c = new();
    end
endmodule
module group_unpacked_19 (
    input logic clk,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] buffer [0:3];
    always_ff @(posedge clk) begin
        buffer[0] <= data_in;
        for (int i=1;i<4;i++) buffer[i] <= buffer[i-1];
        data_out <= buffer[3];
    end
    class buf_c;
        int v;
        function new(); v=0; endfunction
    endclass
    initial begin
        automatic buf_c bc = new();
    end
endmodule
module group_cast_20 (
    input logic [15:0] in_data,
    output logic [3:0] nibble3
);
    typedef logic [3:0] nib_t;
    always_comb begin
        nib_t n [4];
        {n[3], n[2], n[1], n[0]} = in_data;
        nibble3 = n[3];
    end
    class cast_c;
        int x;
        function new(); x=0; endfunction
    endclass
    initial begin
        automatic cast_c cc = new();
    end
endmodule
