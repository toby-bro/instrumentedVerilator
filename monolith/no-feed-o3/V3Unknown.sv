module case_eq_mod (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic equal_case,
    output logic not_equal_case,
    output logic match_constant
);
    localparam [4:0] XCONST = 5'b1x0x1;     
    assign equal_case      = (a === b);     
    assign not_equal_case  = (a !== b);     
    assign match_constant  = (a == XCONST[3:0]);
endmodule
module wild_eq_mod (
    input  logic [3:0] data_in,
    output logic match_wild,
    output logic mismatch_wild
);
    assign match_wild    = (data_in ==? 4'b1x0x);
    assign mismatch_wild = (data_in !=? 4'b0x1x);
endmodule
module isunknown_countbits_mod (
    input  logic [7:0] data_in,
    output logic       is_unknown,
    output logic [3:0] ones_count
);
    assign is_unknown = $isunknown(data_in);
    assign ones_count = $countones(data_in);
endmodule
module bit_select_mod (
    input  logic [7:0] vec_in,
    input  logic [3:0] idx,
    input  logic       bit_in,
    output logic       bit_out
);
    logic [7:0] vec;
    always_comb begin
        vec       = vec_in;
        vec[idx]  = bit_in;    
        bit_out   = vec[idx];  
    end
endmodule
module array_idx_mod (
    input  logic [2:0]  idx,
    input  logic        write_en,
    input  logic [7:0]  write_data,
    output logic [7:0]  read_data
);
    logic [7:0] mem [0:7];
    always_comb begin
        read_data = mem[idx % 8];          
        if (write_en) begin
            mem[idx % 8] = write_data;     
        end
    end
endmodule
module continuous_assign_mod (
    input  logic       in_sig,
    output logic [4:0] out_sig
);
    assign out_sig = in_sig ? 5'bx1x0x : 5'bz0z1z;
endmodule
