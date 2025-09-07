module signed_arith
(
    input  logic signed [7:0] a,
    input  logic signed [7:0] b,
    output logic signed [8:0] sum
);
    assign sum = $signed(a) + $signed(b);
endmodule
module concat_rep
(
    input  logic [3:0] x,
    output logic [7:0] y
);
    assign y = {x,4'hF} ^ {2{x}};
endmodule
module replicate_reduce
(
    input  logic [15:0] bus,
    output logic        parity
);
    assign parity = ^bus;   
endmodule
module shift_dynamic
(
    input  logic [31:0] data,
    input  logic [4:0]  shamt,
    output logic [31:0] out
);
    assign out = data << shamt;
endmodule
module compare_logic
(
    input  logic  signed [7:0] lhs,
    input  logic  signed [7:0] rhs,
    output logic               lt,
    output logic               eq,
    output logic               neq_case
);
    assign lt        = lhs <  rhs;
    assign eq        = lhs == rhs;
    assign neq_case  = lhs !== rhs;   
endmodule
module real_math
(
    input  real r1,
    input  real r2,
    output real rsum,
    output logic greater
);
    always_comb begin
        rsum    = r1 + r2;   
        greater = (r1 > r2); 
    end
endmodule
module string_upper
(
    input  string in_str,
    output string out_str,
    output int    length
);
    always_comb begin
        out_str = in_str.toupper(); 
        length  = in_str.len();     
    end
endmodule
module dyn_array
(
    input  logic       rst,
    input  logic [7:0] din,
    input  int         idx,
    output logic [7:0] dout
);
    byte arr[];
    always_comb begin
        if (rst) begin
            arr = new[4];
            arr = '{default:8'h00};
        end
        else if (idx < arr.size())
            arr[idx] = din;
        dout = (idx < arr.size()) ? arr[idx] : 8'h00;
    end
endmodule
module queue_example
(
    input  logic       clk,
    input  logic       push_en,
    input  logic       pop_en,
    input  logic [7:0] push_d,
    output logic [7:0] pop_d,
    output int         q_size
);
    byte q[$];   
    always_ff @(posedge clk) begin
        if (push_en)
            q.push_back(push_d);
        if (pop_en && q.size() > 0)
            pop_d <= q.pop_front();
        else
            pop_d <= '0;
    end
    always_comb
        q_size = q.size();
endmodule
typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
} n_t;
module struct_concat
(
    input  logic [3:0] in_hi,
    input  logic [3:0] in_lo,
    output n_t         out_s,
    output logic [7:0] as_bus
);
    assign out_s  = '{hi:in_hi, lo:in_lo}; 
    assign as_bus = {in_hi, in_lo};        
endmodule
typedef enum logic [1:0] {IDLE=0, RUN=1, DONE=2} state_e;
module enum_demo
(
    input  state_e state_in,
    output logic   done_flg
);
    assign done_flg = (state_in == DONE);
endmodule
module pattern_demo
(
    input  logic [3:0] nib0,
    input  logic [3:0] nib1,
    output logic [7:0] pat
);
    assign pat = '{nib0,nib1};  
endmodule
module cast_demo
(
    input  logic [3:0]  unsigned_in,
    output logic signed [7:0] signed_out
);
    always_comb signed_out = $signed(unsigned_in); 
endmodule
typedef logic [15:0] word_t;
module typedef_demo
(
    input  word_t a,
    input  word_t b,
    output word_t c
);
    assign c = a ^ b;
endmodule
class simple;
    int v;
    function new(int init);
        v = init;
    endfunction
    function int get();
        return v;
    endfunction
endclass
module class_handle_demo
(
    input  logic trig,
    output int   value
);
    simple s;
    always_comb begin
        if (trig)
            s = new(5);       
        value = (s == null) ? 0 : s.get();
    end
endmodule
