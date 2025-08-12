module concat_packed
  #(parameter WIDTH = 32)
  (input  logic [WIDTH-1:0] in_sig,
   output logic [WIDTH-1:0] out_sig);
    function automatic logic [WIDTH-1:0] make_const();
        logic [15:0] hi;
        logic [15:0] lo;
        {hi, lo} = 32'hDEAD_BEEF;
        hi[15:8] = 8'h12;
        lo[7:0]  = hi[15:8];
        return {hi, lo};
    endfunction
    localparam logic [WIDTH-1:0] CONST_VAL = make_const();
    assign out_sig = in_sig ^ CONST_VAL;
endmodule
module bit_slice_ops
  (input  logic [15:0] in_data,
   output logic [15:0] out_data);
    function automatic logic [15:0] slice_const();
        logic [15:0] tmp;
        tmp = 16'hC0DE;
        tmp[11:4] = 8'hFF;
        return tmp;
    endfunction
    localparam logic [15:0] SLICE_VAL = slice_const();
    assign out_data = in_data & SLICE_VAL;
endmodule
module array_slice_ops
  (input  logic [7:0] inp,
   output logic [15:0] arr_o);
    function automatic logic [15:0] array_const();
        logic [7:0] arr [0:7];
        for (int i = 0; i < 8; i++) begin
            arr[i] = i[7:0];
        end
        arr[5] = 8'hAA;
        arr[4] = 8'hBB;
        arr[3] = 8'hCC;
        return {arr[3], arr[4]};
    endfunction
    localparam logic [15:0] ARRAY_CONST = array_const();
    assign arr_o = ARRAY_CONST ^ {8'h00, inp};
endmodule
module assoc_array_ops
  (input  logic [7:0] in_byte,
   output logic [7:0] out_byte);
    function automatic int build_assoc();
        int a_array [*];
        a_array[5] = 10;
        if (!a_array.exists(3)) begin
            a_array[3] = 7;
        end
        a_array[2] = a_array[5] + a_array[3];
        return a_array[2];
    endfunction
    assign out_byte = in_byte + build_assoc()[7:0];
endmodule
module string_union_ops
  (input  logic en,
   output logic [7:0] char_val);
    typedef union packed {
        logic [31:0] word;
        struct packed {
            logic [7:0] byte0;
            logic [7:0] byte1;
            logic [7:0] byte2;
            logic [7:0] byte3;
        } bytes;
    } packed_u;
    function automatic logic [7:0] string_const();
        string s = "SLANG";
        s[1] = "X";
        return s[1];
    endfunction
    function automatic logic [31:0] union_const();
        packed_u u;
        u.word = 32'hA5A5_F0F0;
        u.bytes.byte2 = 8'hFF;
        return u.word;
    endfunction
    wire [31:0] union_wire;
    assign union_wire = union_const();
    assign char_val = en ? string_const() : union_wire[7:0];
endmodule
