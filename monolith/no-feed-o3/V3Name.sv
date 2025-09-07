//====================================================
module leaf_mod (
    input  logic [7:0] data_in,
    output logic [7:0] data_out
);
    typedef struct packed {
        logic [3:0] low;
        logic [3:0] high;
    } nibbles_t;
    typedef union packed {
        logic   [7:0] raw;
        nibbles_t     nb;
    } union_t;
    union_t u;
    logic [7:0] pub_sig /*verilator public*/;
    always_comb begin
        u.nb.low   = data_in[3:0];
        u.nb.high  = data_in[7:4];
        data_out   = {u.nb.high, u.nb.low};
        pub_sig    = data_out;               
    end
endmodule
//====================================================
module hierarchy_mod (
    input  logic [7:0] dat_i,
    output logic [7:0] dat_o
);
    leaf_mod u_leaf (
        .data_in (dat_i),
        .data_out(dat_o)
    );
endmodule
//====================================================
module class_mod (
    input  logic        clk,
    input  logic [31:0] id_in,
    output logic [31:0] id_out
);
    class packet_c;
        int id;
        function new (int id_i = 0);
            id = id_i;
        endfunction
    endclass
    packet_c pkt;
    always_ff @(posedge clk) begin
        pkt      = new(id_in);
        id_out   <= pkt.id;
    end
endmodule
//====================================================
module dpi_export_mod (
    input  logic [31:0] in_val,
    output logic [31:0] out_val
);
    export "DPI-C" function void sv_exported;
    function void sv_exported (output int dummy);
        dummy = 0;
    endfunction
    always_comb begin
        out_val = in_val;
    end
endmodule
//====================================================
module struct_sel_mod (
    input  logic [15:0] din,
    output logic        flag_out
);
    typedef struct packed {
        logic [7:0] byte0;
        logic [7:0] byte1;
    } inner_t;
    typedef struct packed {
        inner_t inner;
        logic   flag;
    } outer_t;
    outer_t ps;
    always_comb begin
        ps.inner.byte0 = din[7:0];
        ps.inner.byte1 = din[15:8];
        ps.flag        = ^din;     
        flag_out       = ps.flag;
    end
endmodule
