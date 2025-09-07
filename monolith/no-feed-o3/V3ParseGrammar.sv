module child #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);
    assign data_out = data_in;
endmodule
module m_bisonParse (
    input  logic in_sig,
    output logic out_sig
);
    assign out_sig = in_sig;
endmodule
module m_tokenName (
    input  logic [7:0] din,
    output logic [7:0] dout
);
    assign dout = din;
endmodule
module m_candidatePli (
    input  logic [31:0] seed_in,
    output logic [31:0] rand_out
);
    always_comb begin
        rand_out = $urandom(seed_in);
    end
endmodule
module m_parserClear (
    input  logic clk,
    output logic out_flag
);
    logic state;
    always_ff @(posedge clk) begin
        state <= ~state;
    end
    assign out_flag = state;
endmodule
module m_argWrapList (
    input  logic [3:0] in1,
    input  logic [3:0] in2,
    output logic [3:0] sum_out
);
    function automatic logic [3:0] add4 (
        input logic [3:0] a,
        input logic [3:0] b
    );
        add4 = a + b;
    endfunction
    assign sum_out = add4(in1, in2);
endmodule
module m_createSupplyExpr (
    input  logic dummy_in,
    output logic logic_out
);
    supply0 s0_net;
    supply1 s1_net;
    assign logic_out = s0_net | s1_net;
endmodule
module m_scrubRange (
    input  logic [7:0] bus_in,
    output logic [7:0] bus_out
);
    typedef logic [7:0] bus_t;
    bus_t inst_out [1:0];
    child #(.WIDTH(8)) inst_block [1:0] (
        .data_in (bus_in),
        .data_out(inst_out)
    );
    assign bus_out = inst_out[0] ^ inst_out[1];
endmodule
module m_scrubSel (
    input  logic [15:0] data_in,
    output logic [7:0]  data_out
);
    logic [15:0] mem [0:3][0:1];
    assign mem[0][0] = data_in;
    assign data_out  = mem[0][0][7:0];
endmodule
module m_createArray (
    input  logic [3:0] a,
    output logic [3:0] b
);
    logic [3:0][1:0] packed_arr;
    logic [3:0]       dyn_arr[];
    logic [3:0]       q_arr[$];
    assign packed_arr = '{default:4'b0};
    assign b = a;
endmodule
module m_createVariable (
    input  logic trigger,
    output logic flag_out
);
    reg         my_reg;
    integer     my_int;
    time        my_time;
    real        my_real;
    logic [7:0] vector_var;
    always_ff @(posedge trigger) begin
        my_reg      <= ~my_reg;
        my_int      <= my_int + 1;
        my_time     <= $time;
        my_real     <= my_real + 1.0;
        vector_var  <= vector_var + 8'h1;
    end
    assign flag_out = my_reg;
endmodule
module m_unquoteString (
    input  logic in_bit,
    output logic out_bit
);
    string greeting = "Hello,\nVerilator!";
    assign out_bit = in_bit;
endmodule
module m_debug (
    input  logic din,
    output logic dout
);
    assign dout = din;
endmodule
