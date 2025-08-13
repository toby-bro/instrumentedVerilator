`timescale 1ns/1ps
interface bus_if (input logic clk);
    logic [7:0] data;
    modport master (input  data);
    modport slave  (output data);
endinterface
module slice_pack (
    input  logic [15:0] din,
    input  logic  [3:0] sel,
    output logic        dout
);
    logic [7:0] part;
    assign part = din[sel +: 8];   
    assign dout = part[0];         
endmodule
module array_ops (
    input  logic  [1:0] index,
    output logic [31:0] val
);
    logic [3:0][7:0] packed_mem = '{8'hA1, 8'hB2, 8'hC3, 8'hD4};
    int unsigned unpack_mem [0:3] = '{0, 1, 2, 3};
    int dyn_mem [];
    byte queue_mem[$:3] = '{1, 2, 3, 4};
    int assoc_mem[string];
    event ev_sig;
    always_comb begin
        val = packed_mem[index] + unpack_mem[index];
    end
endmodule
class base_c;
    rand int value;
    constraint c_base { value inside {[0:255]}; }
    function int calc();
        return value * 2;
    endfunction
endclass
class child_c extends base_c;
    constraint c_child { value % 2 == 0; }
endclass
module class_ops (
    input  logic dummy,
    output logic [7:0] out
);
    child_c obj;
    always_comb begin
        obj = new();             
        out = obj.calc()[7:0];
    end
endmodule
module assert_mod (
    input  logic clk,
    input  logic rst_n,
    input  logic in_sig,
    output logic out_sig
);
    logic state;
    always_ff @(posedge clk) begin
        if (!rst_n)
            state <= 1'b0;
        else
            state <= in_sig;
    end
    assign out_sig = state;
    property p_change;
        @(posedge clk) disable iff (!rst_n) in_sig |-> ##1 out_sig;
    endproperty
    assert property (p_change);
    cover  property (p_change);
endmodule
module iface_user #(
    parameter int WIDTH = 8
)(
    input  logic             clk,
    input  logic             en,
    output logic [WIDTH-1:0] o
);
    virtual bus_if.master vbus;    
    typedef enum logic [1:0] {IDLE=2'd0, READ=2'd1, DONE=2'd2} state_e;
    state_e state;
    always_ff @(posedge clk) begin
        if (!en)
            state <= IDLE;
        else begin
            unique case (state)
                IDLE : state <= READ;
                READ : state <= DONE;
                default: state <= IDLE;
            endcase
        end
    end
    always_comb begin
        o = (state == READ) ? vbus.data : '0;
    end
endmodule
module struct_mod (
    input  logic [7:0] in_vec,
    output logic [7:0] out_vec
);
    typedef struct packed {
        logic [3:0] hi;
        logic [3:0] lo;
    } nibble_t;
    nibble_t s;
    always_comb begin
        s = nibble_t'(in_vec);   
    end
    assign out_vec = {s.lo, s.hi};
endmodule
