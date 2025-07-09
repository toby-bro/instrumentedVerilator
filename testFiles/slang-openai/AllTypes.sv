module predefined_types_mod(
    input  shortint               in_short,
    input  int signed             in_int,
    input  longint unsigned       in_long,
    input  byte signed            in_byte,
    input  integer                in_integer,
    input  time                   in_time,
    output shortint               out_short,
    output int signed             out_int,
    output longint unsigned       out_long,
    output byte signed            out_byte,
    output integer                out_integer,
    output time                   out_time
);
    always_comb begin
        out_short   = in_short;
        out_int     = in_int;
        out_long    = in_long;
        out_byte    = in_byte;
        out_integer = in_integer;
        out_time    = in_time;
    end
endmodule
module scalar_types_mod(
    input  bit   in_bit,
    input  logic in_logic,
    input  reg   in_reg,
    output bit   out_bit,
    output logic out_logic,
    output reg   out_reg
);
    always_comb begin
        out_bit   = in_bit;
        out_logic = in_logic;
        out_reg   = in_reg;
    end
endmodule
module packed_array_mod(
    input  logic [31:0] in_bus,
    output logic [31:0] out_bus
);
    typedef logic [3:0][7:0] word_t;   
    word_t w;
    always_comb begin
        w       = word_t'(in_bus);
        out_bus = logic'(w);
    end
endmodule
module enum_mod(
    input  logic [1:0] sel,
    output logic       is_two
);
    typedef enum logic [1:0] {
        ZERO  = 2'd0,
        ONE   = 2'd1,
        TWO   = 2'd2,
        THREE = 2'd3
    } state_e;
    state_e state;
    always_comb begin
        state  = state_e'(sel);
        is_two = (state == TWO);
    end
endmodule
module packed_struct_mod(
    input  logic [7:0] in_data,
    input  logic       in_flag,
    output logic [15:0] out_word
);
    typedef struct packed {
        logic         flag;
        logic [7:0]   data;
        logic [6:0]   unused;
    } packed_s;
    packed_s s;
    always_comb begin
        s.flag   = in_flag;
        s.data   = in_data;
        s.unused = 7'd0;
        out_word = s;
    end
endmodule
module unpacked_struct_mod(
    input  logic       clk,
    input  logic [7:0] in_byte,
    output logic [7:0] out_byte
);
    typedef struct {
        logic [7:0] data;
        int         counter;
    } unpk_s;
    unpk_s my_s;
    always_ff @(posedge clk) begin
        my_s.data    <= in_byte;
        my_s.counter <= my_s.counter + 1;
    end
    assign out_byte = my_s.data;
endmodule
module packed_union_mod(
    input  logic [15:0] in_data,
    output logic [15:0] out_data
);
    typedef union packed {
        logic [15:0] by16;
        struct packed {
            logic [7:0] low;
            logic [7:0] high;
        } bytes;
    } packed_u;
    packed_u u;
    always_comb begin
        u.by16   = in_data;
        out_data = {u.bytes.high, u.bytes.low};
    end
endmodule
module type_alias_mod(
    input  logic [3:0] in_nibble,
    output logic [3:0] out_nibble
);
    typedef logic [3:0] nibble_t;
    typedef nibble_t    alias_t;
    alias_t tmp;
    always_comb begin
        tmp        = in_nibble;
        out_nibble = tmp;
    end
endmodule
module class_mod(
    input  bit in_sig,
    output bit out_sig
);
    class simple_c;
        bit value;
        function void set(bit v); value = v; endfunction
        function bit  get();      return value; endfunction
    endclass
    simple_c c_handle;
    always_comb begin
        if (c_handle == null)
            c_handle = new();
        c_handle.set(in_sig);
        out_sig = c_handle.get();
    end
endmodule
