typedef struct {
    logic [7:0]  a;
    logic [15:0] b;
} data_s;
typedef union {
    logic [31:0]          w;
    struct {
        logic [7:0]  l;
        logic [23:0] h;
    } parts;
} uni_u;
interface ctrl_if;
    logic valid;
    logic ready;
    modport passive (input valid, ready);
endinterface
class pkt;
    rand bit [7:0]  id;
    bit  [31:0] data;
    function new(bit [7:0] id_i, bit [31:0] data_i);
        id   = id_i;
        data = data_i;
    endfunction
endclass
class pkt_ext extends pkt;
    bit [15:0] crc;
    function new(bit [7:0] id_i, bit [31:0] data_i);
        super.new(id_i, data_i);
        crc = ^{id_i, data_i};
    endfunction
endclass
module class_user (
    input  logic [7:0]  id_i,
    input  logic [31:0] data_i,
    output logic [15:0] crc_o
);
    always_comb begin
        pkt_ext p = new(id_i, data_i);
        crc_o = p.crc;
    end
endmodule
module struct_user (
    input  logic [7:0]  in_a,
    input  logic [15:0] in_b,
    output logic [23:0] sum_o
);
    data_s s;
    always_comb begin
        s.a = in_a;
        s.b = in_b;
        sum_o = {s.a, s.b};
    end
endmodule
module union_user (
    input  logic [31:0] in_w,
    output logic [7:0]  lower_o
);
    uni_u u;
    always_comb begin
        u.w = in_w;
        lower_o = u.parts.l;
    end
endmodule
module wide_user (
    input  logic [1023:0] wide_in,
    output logic [9:0]    popcnt_o
);
    integer k;
    always_comb begin
        popcnt_o = 0;
        for (k = 0; k < 1024; k++) begin
            popcnt_o += wide_in[k];
        end
    end
endmodule
module ifc_user (
    input  logic clk_i,
    input  logic rst_i,
    output logic ready_o
);
    ctrl_if ifc();
    always_comb begin
        ready_o = ifc.ready & ~rst_i;
    end
endmodule
