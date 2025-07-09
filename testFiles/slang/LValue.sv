module bit_slice_mod(
    input  logic [31:0] in_val,
    output logic [31:0] out_val
);
    function automatic int f_bitslice();
        bit [15:0] x;
        x = 16'hABCD;
        x[11:8] = 4'h0;
        return int'(x);
    endfunction
    assign out_val = in_val ^ f_bitslice();
endmodule
module concat_mod(
    input  logic [7:0] data_in,
    output logic [7:0] data_out
);
    function automatic byte f_concat();
        logic [3:0] a;
        logic [3:0] b;
        {a, b} = 8'hA5;
        return {a, b};
    endfunction
    assign data_out = data_in ^ f_concat();
endmodule
module array_index_mod(
    input  logic [31:0] in_val,
    output logic [31:0] out_val
);
    function automatic int f_element_index();
        int arr[0:3];
        arr = '{0, 1, 2, 3};
        arr[2] = 7;
        return arr[2];
    endfunction
    assign out_val = in_val + f_element_index();
endmodule
module array_slice_mod(
    input  logic [31:0] in_val,
    output logic [31:0] out_val
);
    function automatic int f_array_slice();
        int arr[0:7];
        int slice[0:3];
        for (int i = 0; i < 8; i++) arr[i] = i;
        slice = arr[4+:4];
        slice[1] = 99;
        return slice[1];
    endfunction
    assign out_val = in_val ^ f_array_slice();
endmodule
module queue_const_mod(
    input  logic [31:0] in_val,
    output logic [31:0] out_val
);
    function automatic int f_queue();
        int q[$];
        q.push_back(1);
        q.push_back(2);
        q.push_back(3);
        q[1] = 5;
        q.push_back(9);
        return q.size();
    endfunction
    assign out_val = in_val - f_queue();
endmodule
module assoc_array_mod(
    input  logic [31:0] in_val,
    output logic [31:0] out_val
);
    function automatic int f_assoc();
        int aa[int];
        int val5;
        aa[10] = 20;
        if (aa.exists(5))
            val5 = aa[5];
        else
            val5 = 42;
        return val5 + aa[10];
    endfunction
    assign out_val = in_val ^ f_assoc();
endmodule
module union_mod(
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    typedef union packed {
        bit [31:0] w;
        bit [31:0] v;
    } u32_t;
    function automatic byte f_union_local();
        u32_t u;
        u.w = 32'hCAFEBABE;
        u.v[15:8] = 8'h55;
        return byte'(u.v[15:8]);
    endfunction
    assign out_val = in_val | f_union_local();
endmodule
