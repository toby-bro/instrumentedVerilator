module element_select_const
(
    input  logic [7:0] in_data,
    output logic       out_bit
);
    assign out_bit = in_data[3];
endmodule
module element_select_var
(
    input  logic [7:0] in_data,
    input  logic [2:0] index,
    output logic       out_bit
);
    assign out_bit = in_data[index];
endmodule
module range_select_simple
(
    input  logic [31:0] in_data,
    output logic [7:0]  out_slice
);
    assign out_slice = in_data[15:8];
endmodule
module range_select_indexed_up
(
    input  logic [31:0] in_data,
    input  logic [3:0]  base,
    output logic [7:0]  out_slice
);
    assign out_slice = in_data[base +: 8];
endmodule
module range_select_indexed_down
(
    input  logic [31:0] in_data,
    input  logic [3:0]  base,
    output logic [7:0]  out_slice
);
    assign out_slice = in_data[base -: 8];
endmodule
module struct_member_access
(
    input  logic [31:0] in_word,
    output logic [7:0]  out_field
);
    typedef struct packed {
        logic [7:0]  a;
        logic [7:0]  b;
        logic [15:0] c;
    } my_s_t;
    my_s_t s;
    assign s       = in_word;
    assign out_field = s.a;
endmodule
module packed_union_select
(
    input  logic [31:0] in_word,
    input  logic        hi_sel,
    output logic [15:0] out_half
);
    typedef union packed {
        struct packed {
            logic [15:0] lo;
            logic [15:0] hi;
        } parts;
        logic [31:0] full;
    } u_t;
    u_t u;
    assign u.full  = in_word;
    assign out_half = hi_sel ? u.parts.hi : u.parts.lo;
endmodule
module class_member_access
(
    input  logic        trig,
    output logic [15:0] out_id
);
    class Packet;
        rand logic [15:0] id;
        function void set_id(logic [15:0] new_id);
            id = new_id;
        endfunction
        function logic [15:0] get_id();
            return id;
        endfunction
    endclass
    Packet p;
    always_comb begin
        p = new();
        p.set_id(16'h1234);
        out_id = p.get_id();
    end
endmodule
module associative_array_access
(
    input  logic [31:0] in_key,
    output logic [31:0] out_val
);
    typedef int int_t;
    int_t aa[int];
    always_comb begin
        aa[int'(in_key)] = int'(in_key) + 1;
        out_val          = aa[int'(in_key)];
    end
endmodule
module string_index_select
(
    input  logic [7:0] idx,
    output logic [7:0] out_char
);
    string s = "SystemVerilog";
    always_comb begin
        out_char = s[int'(idx)];
    end
endmodule
module unpacked_array_select
(
    input  logic [7:0] in_vec,
    output logic [7:0] out_elem
);
    logic [7:0] vec_array [0:3];
    assign vec_array[0] = in_vec;
    assign out_elem     = vec_array[0];
endmodule
