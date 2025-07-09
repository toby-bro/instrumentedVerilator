package type_pkg;
    typedef struct packed { logic [7:0] data; bit parity; } packed_s_t;
    typedef union { logic [31:0] word; logic [7:0] bytes [4]; } packed_u_t;
    typedef enum logic [1:0] { RED = 2'b00, GREEN = 2'b01, BLUE = 2'b10, WHITE = 2'b11 } color_e;
endpackage
module integral_types_mod #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in_data,
    output logic [WIDTH-1:0] out_data
);
    import type_pkg::*;
    bit   signed [7:0]   bit_vec;
    logic signed [15:0]  logic_vec;
    reg   [31:0]         reg_vec;
    byte                 byte_var;
    shortint             short_var;
    int                  int_var;
    longint unsigned     long_var;
    integer              legacy_int;
    time                 time_var;
    string               str_var;
    chandle              ch_var;
    event                ev_var;
    assign out_data = in_data;
    class simple_class;
        int v;
        function new(); v = 0; endfunction
    endclass
    simple_class sc;
    always_comb begin
        sc = new();
        bit_vec = in_data[7:0];
        reg_vec = {24'h0, in_data};
    end
endmodule
module array_types_mod (
    input  logic [1:0] sel,
    output logic       match_flag
);
    typedef logic [7:0] byte_t;
    byte_t uarray [0:3];
    logic [15:0] word_array [0:1][0:3];
    logic [3:0][7:0] packed_vec;
    assign match_flag = (uarray[sel] == 8'hFF);
    class array_dummy;
        int i;
        function new(); i = 0; endfunction
    endclass
    array_dummy ad;
    always_comb begin
        ad = new();
        uarray[sel] = 8'hAA;
        packed_vec  = '0;
    end
endmodule
module struct_union_mod (
    input  logic       clk,
    output logic [7:0] out_byte
);
    typedef struct packed { logic [7:0] data; logic parity; } p_s_t;
    typedef struct { int unsigned cnt; byte bytes [4]; } u_s_t;
    typedef union { logic [7:0] octet; logic [3:0] nibs [1:0]; } p_u_t;
    p_s_t ps;
    u_s_t us;
    p_u_t pu;
    assign out_byte = ps.data;
    class struct_dummy;
        string n;
        function new(); n = ""; endfunction
    endclass
    struct_dummy sd;
    always_ff @(posedge clk) begin
        sd = new();
        ps.data   <= 8'h55;
        ps.parity <= ^8'h55;
        us.cnt    <= us.cnt + 1;
        pu.octet  <= ps.data;
    end
endmodule
module enum_mod (
    input  logic [1:0] color_in,
    output logic       is_green
);
    typedef enum logic [1:0] { RED = 0, GREEN = 1, BLUE = 2, WHITE = 3 } color_e;
    color_e c_var;
    assign is_green = (c_var == GREEN);
    class enum_dummy;
        color_e c;
        function new(); c = RED; endfunction
    endclass
    enum_dummy ed;
    always_comb begin
        ed = new();
        c_var = color_e'(color_in);
    end
endmodule
module class_mod (
    input  logic [7:0] in_v,
    output logic [7:0] out_v
);
    class base_c;
        rand int unsigned x;
        function int get(); return x; endfunction
    endclass
    class derived_c extends base_c;
        rand int unsigned y;
        function int sum(); return x + y; endfunction
    endclass
    derived_c d_handle;
    assign out_v = in_v;
    always_comb begin
        d_handle = new();
        d_handle.x = in_v;
        d_handle.y = in_v + 1;
    end
endmodule
