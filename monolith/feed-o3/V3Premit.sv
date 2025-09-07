module wide_const_pool (
    input  logic        dummy_in,
    output logic [511:0] out_data
);
    assign out_data = 512'h0123456789ABCDEF_FEDCBA9876543210_0011223344556677_8899AABBCCDDEEFF_0123456789ABCDEF_FEDCBA9876543210_0011223344556677_8899AABBCCDDEEFF;
endmodule
module shift_overlay (
    input  logic [31:0] in_data,
    input  logic [5:0]  shift_amt,
    output logic [31:0] out_left,
    output logic [31:0] out_right,
    output logic [31:0] out_arith
);
    assign out_left  = in_data <<  shift_amt;
    assign out_right = in_data >>  shift_amt;
    assign out_arith = $signed(in_data) >>> shift_amt;
endmodule
module cond_wide_temp (
    input  logic [127:0] a,
    input  logic [127:0] b,
    input  logic [127:0] c,
    input  logic [127:0] d,
    output logic [255:0] result
);
    assign result = ((a + b) > (c - d)) ? {a, b} : {c, d};
endmodule
module dep_assign (
    input  logic        clk,
    input  logic [15:0] in_val,
    output logic [15:0] out_val
);
    always_ff @(posedge clk) begin
        out_val <= out_val + in_val;
    end
endmodule
module array_packed_conv (
    input  logic        clk,
    input  logic        wr_en,
    input  logic [3:0]  wr_idx,
    input  logic [7:0]  wr_data,
    input  logic [3:0]  rd_idx,
    output logic [7:0]  rd_data
);
    logic [7:0] mem_array [0:15];
    logic [127:0] packed_mem;
    always_ff @(posedge clk) begin
        if (wr_en) mem_array[wr_idx] <= wr_data;
    end
    always_comb begin
        packed_mem = {<<8{mem_array}};
    end
    assign rd_data = packed_mem[rd_idx * 8 +: 8];
endmodule
module while_loop_logic (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [7:0]  limit,
    output logic [7:0]  count
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            count <= 8'd0;
        end else begin
            int i;
            i = 0;
            while (i < limit) begin
                i++;
                if (i > 8'd255) begin
                    i = limit;
                end
            end
            count <= limit;
        end
    end
endmodule
module assoc_sel_mod (
    input  logic        clk,
    input  int          key_in,
    output logic [7:0]  value_out
);
    typedef logic [7:0] byte_t;
    byte_t assoc_array [int];
    always @(posedge clk) begin
        assoc_array[key_in] = key_in[7:0];
        value_out           = assoc_array[key_in];
    end
endmodule
