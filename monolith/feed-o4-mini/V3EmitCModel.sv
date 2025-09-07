`ifndef EMITHEADER_GUARD
`define EMITHEADER_GUARD
module emitHeader_mod #(parameter SYS_VER=1, parameter WITH_MT=0)(
    input  logic [3:0] in_sig,
    output logic [3:0] out_sig
);
generate
    if (SYS_VER) begin : gen_header
        localparam string HEADER_NAME = "Model";
        wire flag = WITH_MT;
        assign out_sig = (in_sig & {4{flag}});
    end else begin : gen_noheader
        assign out_sig = in_sig;
    end
endgenerate
endmodule
`endif
module findFuncps_mod(
    input  logic [7:0] arr_in [0:3],
    output logic [7:0] arr_out [0:3]
);
logic [7:0] temp [0:3];
always_comb begin
    int i, j;
    for (i = 0; i < 4; i++) begin
        temp[i] = arr_in[i];
    end
    for (i = 0; i < 4; i++) begin
        for (j = 0; j < 3; j++) begin
            if (temp[j] > temp[j+1]) begin
                logic [7:0] t;
                t = temp[j];
                temp[j] = temp[j+1];
                temp[j+1] = t;
            end
        end
    end
    for (i = 0; i < 4; i++) begin
        arr_out[i] = temp[i];
    end
end
endmodule
module emitConstructor_mod(
    input  logic       clk,
    input  logic       rst,
    output logic [1:0] state_out
);
logic [3:0] multi [0:1][0:1];
class MyCls;
    rand logic [1:0] val;
    function void work(input logic [1:0] in);
        val = in;
    endfunction
endclass
MyCls obj;
always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
        for (int a = 0; a < 2; a++) begin
            for (int b = 0; b < 2; b++) begin
                multi[a][b] <= a + b;
            end
        end
        obj = new;
    end else begin
        obj.work(multi[0][1]);
        state_out <= obj.val;
    end
end
endmodule
module emitDestructor_mod(
    input  logic trigger,
    output logic done
);
class TempCls;
    function void action();
        done = 1;
    endfunction
    function void destroy();
    endfunction
endclass
TempCls t_inst;
always_ff @(posedge trigger) begin
    t_inst = new;
    t_inst.action();
    t_inst.destroy();
end
endmodule
`ifdef VL_DEBUG
module stdMethods1_mod(
    input  logic clk,
    input  logic rst_n,
    output logic ok
);
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        ok <= 1'b0;
    end else begin
        assert(rst_n) else ok <= 1'b0;
        ok <= 1'b1;
    end
end
endmodule
`endif
module stdMethods2_mod(
    input  logic        clk,
    input  logic        en,
    output logic        pending,
    output logic [31:0] nextSlot
);
int delay_queue[$];
function logic hasPending();
    return (delay_queue.size() > 0);
endfunction
function int nextTime();
    return delay_queue[0];
endfunction
always_ff @(posedge clk) if (en) begin
    delay_queue.push_back($urandom_range(100,0));
end
assign pending  = hasPending();
assign nextSlot = hasPending() ? nextTime() : 0;
endmodule
module traceMethods_mod(
    input  logic en,
    output logic ok
);
import "DPI-C" function void dpi_trace_decl_types(input int a);
import "DPI-C" function void dpi_trace_init_top(input int self, input int tp);
function void trace_init(input int voidSelf, input int tracep, input int code);
    ok = (code == 1);
endfunction
always_comb begin
    if (en) begin
        dpi_trace_decl_types(10);
        dpi_trace_init_top(en, 20);
        trace_init(0, 30, 1);
    end
end
endmodule
module serialization_mod(
    input  logic clk,
    input  logic start,
    output logic ser_done,
    output logic deser_done
);
function automatic logic [7:0] to_serialize(input logic [7:0] in_data);
    return in_data ^ 8'hFF;
endfunction
task automatic serialize(input logic [7:0] data);
    ser_done <= 1;
endtask
task automatic deserialize(output logic [7:0] data);
    data = 8'h00;
    deser_done <= 1;
endtask
always_ff @(posedge clk) if (start) begin
    logic [7:0] d;
    d = to_serialize(8'hA5);
    serialize(d);
    deserialize(d);
end
endmodule
module dpiDispatcher_mod(
    input  logic in_sig,
    output logic out_sig
);
import "DPI-C" function int ext_dispatch(input int code);
always_comb begin
    int res;
    res = ext_dispatch(in_sig);
    out_sig = res[0];
end
endmodule
