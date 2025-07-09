interface simple_if #(parameter WIDTH = 8);
    logic clk;
    logic [WIDTH-1:0] data;
endinterface
module m_param_ports
#(
    parameter int WIDTH = 8,
    parameter type T = logic [WIDTH-1:0]
)
(
    input  logic                   clk,
    input  logic                   rst,
    input  logic [WIDTH-1:0]       in_data,
    output logic [WIDTH-1:0]       out_data
);
    T data_reg;
    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            data_reg <= '0;
        else
            data_reg <= in_data;
    end
    assign out_data = data_reg;
endmodule
module m_net_strength
(
    input  logic in_bit,
    output logic out_bit
);
    wire (strong1, weak0) driven_net = in_bit;
    assign out_bit = driven_net;
endmodule
module m_struct_enum
(
    input  logic [3:0] sel,
    output logic [7:0] value
);
    typedef enum logic [1:0] {
        IDLE = 2'd0,
        RUN  = 2'd1,
        STOP = 2'd2
    } state_e;
    typedef struct packed {
        logic [7:0] data;
        logic       valid;
    } packet_s;
    state_e  state;
    packet_s packet;
    always_comb begin
        case (sel)
            4'd0: value = packet.data;
            4'd1: value = {6'd0, state};
            default: value = 8'hFF;
        endcase
    end
endmodule
module m_inout_bus
(
    input  logic       enable,
    inout  logic [7:0] data_bus,
    output logic [7:0] mirror
);
    assign mirror   = data_bus;
    assign data_bus = enable ? mirror : 'z;
endmodule
(* attr_module = "demo" *)
module m_attributes_data
(
    (* port_attr = 1 *) input  logic a,
    (* port_attr = 2 *) output logic b
);
    wire logic temp;
    assign temp = a;
    assign b    = temp;
endmodule
module m_static_automatic
(
    input  logic clk,
    input  logic din,
    output logic dout
);
    always_ff @(posedge clk) begin : blk
        automatic int   cnt = 0;
        static   logic  state;
        cnt   = cnt + (din ? 1 : 0);
        state <= din;
        dout  <= state ^ cnt[0];
    end
endmodule
module m_dimension
(
    input  logic [7:0] in_data [0:3],
    output logic [7:0] out_data [0:3]
);
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : gen_blk
            assign out_data[i] = in_data[i];
        end
    endgenerate
endmodule
module m_interface_usage
(
    input  logic       clk,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    simple_if #(8) sif();
    assign sif.clk = clk;
    always_ff @(posedge clk) begin
        sif.data <= din;
    end
    assign dout = sif.data;
endmodule
