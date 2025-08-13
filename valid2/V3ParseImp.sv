`timescale 1ns/1ps
package util_pkg;
    function automatic int add(input int a, input int b);
        add = a + b;
    endfunction
endpackage
package mypkg;
    typedef logic [7:0] byte_t;
    virtual class base_class;
        pure virtual function void foo();
    endclass
endpackage
interface simple_if(input logic clk);
    logic sig;
endinterface
module timescale_mod (
    input  logic a,
    output logic b
);
    assign b = a;
endmodule
module strength_gate_mod (
    input  logic in,
    output logic out
);
    buf (strong1, weak0) buf_inst (out, in);
endmodule
module colon_begin_mod (
    input  logic        clk,
    input  logic        din,
    output logic        dout
);
    always_ff @(posedge clk) BEGIN_LBL: begin
        dout <= din;
    end
endmodule
module virtual_interface_mod (
    input  logic clk,
    output logic sig
);
    virtual simple_if vif;
    mypkg::byte_t data;
    always_comb begin
        sig  = clk;
        data = 8'h55;
    end
endmodule
module new_with_mod (
    input  logic       clk,
    output logic [1:0] value
);
    class RandC;
        bit [1:0] val;
        function new();
            val = 2'b00;
        endfunction
        function void inc();
            val = val + 1;
        endfunction
    endclass
    RandC obj;
    always_ff @(posedge clk) begin
        if (obj == null) obj = new;
        obj.inc();
        value <= obj.val;
    end
endmodule
module mailbox_mod (
    input  logic       clk,
    input  logic       wr,
    output logic [7:0] q
);
    mailbox #(logic [7:0]) mb;
    logic [7:0] tmp;
    always_ff @(posedge clk) begin
        if (mb == null) mb = new;
        if (wr) begin
            tmp = 8'hAA;
            mb.put(tmp);
        end
        if (mb.num() > 0) mb.get(q);
    end
endmodule
module semaphore_mod (
    input  logic clk,
    output logic available
);
    semaphore sem;
    always_ff @(posedge clk) begin
        if (sem == null) sem = new;
        available <= (sem.try_get());
        if (available) sem.put();
    end
endmodule
module process_mod (
    input  logic clk,
    output logic busy
);
    process p_handle;
    always_ff @(posedge clk) begin
        p_handle = process::self();
        busy <= (p_handle != null);
    end
endmodule
