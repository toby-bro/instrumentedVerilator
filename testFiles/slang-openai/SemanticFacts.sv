`timescale 1ns/1ps
typedef class dummy_fwd;
class dummy_fwd;
    int value;
endclass
interface bus_if;
    logic        data;
    logic        valid;
    logic [7:0]  payload;
    modport master (input data, output valid, output payload);
    modport slave  (output data, input valid, input payload);
endinterface
module procedural_examples(
    input  logic clk,
    input  logic rst_n,
    input  logic data_in,
    output logic data_out
);
    function logic static_fun(input logic din);
        static int counter = 0;
        counter++;
        static_fun = din ^ counter[0];
    endfunction
    function automatic logic auto_fun(input logic din);
        auto_fun = din;
    endfunction
    task automatic dir_task(
        input  logic       din,
        inout  logic [3:0] io,
        output logic       dout,
        ref    logic       ref_sig
    );
        dout    = din;
        io      = io + 1;
        ref_sig = ~ref_sig;
    endtask
    logic [3:0] tmp_io;
    logic       ref_comb;
    logic       latch_var;
    logic       comb_result;
    logic       ff_var;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            data_out <= 1'b0;
        else
            data_out <= static_fun(data_in);
    end
    always_comb begin
        tmp_io       = 4'h0;
        ref_comb     = 1'b0;
        comb_result  = 1'b0;
        dir_task(data_in, tmp_io, comb_result, ref_comb);
    end
    always_latch begin
        if (!rst_n)
            latch_var = 1'b0;
    end
    always @(posedge clk) begin
        ff_var <= ~ff_var;
    end
endmodule
module net_strength_examples(
    input  wire in_sig,
    output wire out_sig
);
    trireg (small)  reg_small;
    trireg (medium) reg_medium;
    trireg (large)  reg_large;
    wire (strong1, weak0) drv_net = 1'b0;
    assign reg_small  = in_sig;
    assign reg_medium = reg_small;
    assign reg_large  = reg_medium;
    assign drv_net    = reg_large;
    assign out_sig    = drv_net;
    specify
        pulsestyle_onevent  out_sig;
        pulsestyle_ondetect out_sig;
    endspecify
endmodule
module case_conditions(
    input  logic [1:0] sel,
    output logic       y
);
    always_comb begin
        case (sel)
            2'b00: y = 1'b0;
            2'b01: y = 1'b1;
            default: y = 1'b0;
        endcase
        casez (sel)
            2'b1?: y = 1'b1;
            default: ;
        endcase
        casex (sel)
            2'bx1: y = 1'b0;
            default: ;
        endcase
    end
endmodule
module block_variants(
    input  logic start,
    output logic done
);
    always @(start) begin : seq_start
        fork : par_block_1
            done = start;
            done = ~start;
        join_any
        fork : par_block_2
            done = 1'b1;
        join_none
        disable par_block_2;
    end
endmodule
module assertion_examples(
    input  logic clk,
    input  logic rst_n,
    input  logic sig_in,
    output logic sig_out
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            sig_out <= 1'b0;
        else
            sig_out <= sig_in;
    end
    always @(posedge clk) begin
        assert (sig_out !== 1'bx);
        assume (sig_out == sig_out);
        cover  (sig_out);
    end
    property stable_p;
        @(posedge clk) disable iff (!rst_n) sig_out == $past(sig_out);
    endproperty
    assert property (stable_p);
    assume property (stable_p);
    cover  property (stable_p);
endmodule
class simple_class;
    int stored;
    function new(int v = 0);
        stored = v;
    endfunction
endclass
module class_usage(
    input  logic clk,
    output logic [31:0] class_value
);
    simple_class c;
    logic        init_done = 1'b0;
    always_ff @(posedge clk) begin
        if (!init_done) begin
            c = new(32'h1234);
            init_done <= 1'b1;
        end
        if (c != null)
            class_value <= c.stored;
    end
endmodule
