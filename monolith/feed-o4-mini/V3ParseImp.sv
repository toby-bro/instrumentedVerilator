`timescale 1ns/10ps
`line 100
`line 200
`define TEST
`define FOOBAR
`ifdef TEST
`endif
module m_mailbox(input logic clk, output logic done);
    mailbox mb;
    always_comb begin
        mb = new();
    end
    assign done = clk;
endmodule
module m_random(input logic in_sig, output logic out_sig);
    function bit randomize();
        return 1;
    endfunction
    always_comb begin
        if (randomize())
            out_sig = 1;
        else
            out_sig = 0;
    end
endmodule
module m_std_pkg(input logic x, output logic y);
    import std::*;
    assign y = x;
endmodule
module m_semaphore(input logic a, output logic b);
    semaphore sem;
    always_comb begin
        sem = new();
    end
    assign b = a;
endmodule
module m_tag(input logic a, output logic b);
    /*verilator tag MY_UNIQUE_TAG*/
    assign b = a;
endmodule
module m_lint(input logic a, output logic b);
    /*verilator lint_save*/
    /*verilator lint_off UNUSED*/
    /*verilator lint_restore*/
    assign b = a;
endmodule
module m_badlint(input logic a, output logic b);
    /*verilator bad-comment*/
    assign b = a;
endmodule
module m_pp(input logic a, output logic b);
    `define MACRO1 1
    `ifdef MACRO1
    `endif
    `ifdef UNUSED
    `unknown_directive
    `endif
    `undef MACRO1
    assign b = a;
endmodule
module m_time(input logic clk, output logic done);
    localparam time T = 123ps;
    assign done = clk;
endmodule
module m_strength(input logic a, output logic b);
    wire (pull0, pull1) w = 1'b0;
    assign b = a;
endmodule
