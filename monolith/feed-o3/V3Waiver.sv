module width_mismatch (
    input  logic [3:0] in_data,
    output logic [7:0] out_data
);
    assign out_data = in_data;   
endmodule
module unused_warn (
    input  logic in_sig,
    output logic out_sig
);
    logic unused_signal_a;
    logic unused_signal_b;
    assign out_sig = in_sig;
endmodule
module real_cvt (
    input  logic in_bit,
    output logic out_bit
);
    real r_val;
    int  i_val;
    always_comb begin
        i_val = r_val;   
        r_val = i_val;   
    end
    assign out_bit = in_bit;
endmodule
module case_incomplete (
    input  logic [1:0] sel,
    output logic       out_flag
);
    always_comb begin
        case (sel)
            2'b00: out_flag = 1'b0;
            2'b01: out_flag = 1'b1;
        endcase                 
    end
endmodule
module case_overlap (
    input  logic [1:0] sel,
    output logic [1:0] out_vec
);
    always_comb begin
        case (sel)
            2'b00,
            2'b00: out_vec = 2'b00;   
            default: out_vec = 2'b11;
        endcase
    end
endmodule
module undriven_sig (
    input  logic in_line,
    output logic out_line
);
    logic orphan_sig;   
    assign out_line = in_line;
endmodule
module overwidth_const (
    input  logic        dummy_in,
    output logic [3:0]  data_out
);
    assign data_out = 8'hFF;   
endmodule
module blk_and_nblk (
    input  logic clk,
    input  logic data_in,
    output logic data_out
);
    always_ff @(posedge clk) begin
        data_out =  data_in;   
        data_out <= data_in;   
    end
endmodule
module latch_test (
    input  logic [1:0] a,
    output logic       b
);
    always_comb begin
        if (a[1]) b = a[0];    
    end
endmodule
