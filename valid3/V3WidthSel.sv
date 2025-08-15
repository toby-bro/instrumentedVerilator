module m_selbit_basic(
    input  logic [31:0] in_vec,
    input  logic [4:0]  idx,
    output logic        bit_out
);
    assign bit_out = in_vec[idx];
endmodule
module m_selbit_unpacked(
    input  logic [1:0] idx,
    output logic [7:0] element
);
    logic [7:0] mem [0:3];
    assign element = mem[idx];
endmodule
module m_selbit_packed(
    input  logic [1:0] idx,
    output logic [7:0] element
);
    logic [3:0][7:0] pdata;
    assign element = pdata[idx];
endmodule
module m_selextract_basic(
    input  logic [31:0] in_vec,
    output logic [7:0]  slice_out
);
    assign slice_out = in_vec[15:8];
endmodule
module m_selplus(
    input  logic [31:0] in_vec,
    input  logic [4:0]  base,
    output logic [7:0]  slice
);
    assign slice = in_vec[base +: 8];
endmodule
module m_selminus(
    input  logic [31:0] in_vec,
    input  logic [4:0]  base,
    output logic [7:0]  slice
);
    assign slice = in_vec[base -: 8];
endmodule
module m_sel_queue(
    input  logic [4:0] idx,
    output byte        data_out
);
    byte unsigned q[$];
    always_comb begin
        if (idx < q.size())
            data_out = q[idx];
        else
            data_out = 8'd0;
    end
endmodule
module m_sel_queue_back(
    input  logic enable,
    output byte data_last
);
    byte unsigned q[$];
    always_comb begin
        if (enable && q.size() != 0)
            data_last = q[$ - 1];
        else
            data_last = 8'd0;
    end
endmodule
module m_sel_dynamic_array(
    input  logic [4:0] idx,
    output int         data_out
);
    int dyn_array[];
    always_comb begin
        if (idx < dyn_array.size())
            data_out = dyn_array[idx];
        else
            data_out = 0;
    end
endmodule
module m_sel_string(
    input  logic [31:0] idx,
    output byte         char_out
);
    string s;
    always_comb begin
        if (idx < s.len())
            char_out = s[idx];
        else
            char_out = 8'd0;
    end
endmodule
module m_slice_packed_array(
    input  logic [4:0]  base,
    output logic [15:0] slice_out
);
    logic [31:0] pack_vec;
    assign slice_out = pack_vec[base +: 16];
endmodule
