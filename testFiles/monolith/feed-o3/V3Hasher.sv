interface bus_if;
    logic req;
    logic gnt;
    modport master (input gnt, output req);
    modport slave  (input req, output gnt);
endinterface
import "DPI-C" context function int c_add (input int a, input int b);
class base_cls;
    rand bit x;
    function void foo(); endfunction
endclass
class drv_cls extends base_cls;
    rand bit y;
    function int bar(); return y; endfunction
endclass
typedef enum logic [1:0] {S0 = 2'd0, S1 = 2'd1, S2 = 2'd2} state_e;
module array_types #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in_data,
    output logic [WIDTH-1:0] out_data
);
    logic [WIDTH-1:0] packed_arr [0:3];
    int dyn_arr [];
    int q[$];
    int aa [string];
    int wildcard_arr [*];
    bit unsized_arr [];
    chandle ch_ptr;
    logic [WIDTH-1:0] tmp;
    always_comb begin
        if (aa.exists("key")) tmp = int'(aa["key"]);
        else                  tmp = {<<{in_data}};
        out_data = tmp;
        dyn_arr  = new[4];
        q.push_back(in_data);
    end
endmodule
module class_usage (
    input  logic       clk,
    input  logic [7:0] in_byte,
    output logic [7:0] out_byte
);
    drv_cls d_handle;
    task automatic do_task(input logic [7:0] v); endtask
    always_comb begin
        if (d_handle == null) d_handle = new();
        out_byte = c_add(in_byte, d_handle.bar());
        do_task(out_byte);
        assert (out_byte == out_byte);
    end
endmodule
module interface_mod (
    input  logic dummy,
    output logic o
);
    bus_if bus();
    assign bus.req = dummy;
    assign o       = bus.gnt;
endmodule
module modport_user (
    input  logic en,
    output logic done
);
    bus_if bus();
    task automatic toggle();
        bus.req = ~bus.req;
    endtask
    always_comb begin
        if (en) toggle();
        done = bus.req & bus.gnt;
    end
endmodule
module enum_cast_sel (
    input  logic [3:0] in_val,
    output state_e     state_out
);
    state_e current_state;
    always_comb begin
        current_state = state_e'(in_val[1:0]);
        state_out     = current_state;
    end
endmodule
module struct_stream (
    input  logic [31:0] data_in,
    output logic [31:0] data_out
);
    typedef struct packed {
        logic [15:0] hi;
        logic [15:0] lo;
    } halves_t;
    halves_t hs;
    always_comb begin
        hs       = halves_t'(data_in);
        data_out = {hs.lo, hs.hi};
    end
endmodule
module sens_tree (
    input  logic clk,
    input  logic rst_n,
    output logic q
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) q <= 1'b0;
        else        q <= ~q;
    end
endmodule
