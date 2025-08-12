checker simple_chk (input logic sig);
    always_comb begin
        assert(sig == sig);
    end
endchecker
module mod_disable(
    input  logic       clk,
    output logic [3:0] y
);
    always_ff @(posedge clk) begin : blk
        static integer i = 0;
        i = i + 1;
        y <= i[3:0];
        if (i == 4) begin
            disable blk;
        end
    end
endmodule
module mod_wait_fork(
    input  logic trigger,
    output logic done
);
    event ev1, ev2;
    initial begin : main
        fork : parallel_block
            -> ev1;
            -> ev2;
        join_none
        wait fork;
        wait_order (ev1, ev2) begin
            done = 1'b1;
        end else begin
            done = 1'b0;
        end
        disable fork;
    end
endmodule
module mod_proc_assign(
    input  logic clk,
    output logic reg_out
);
    logic tmp;
    initial begin
        assign   tmp = 1'b0;
        deassign tmp;
        force    tmp = 1'b1;
        release  tmp;
    end
    always_ff @(posedge clk) begin
        reg_out <= tmp;
    end
endmodule
module mod_rand(
    input  logic [3:0] sel,
    output logic       out
);
    logic rs_tmp;
    always_comb begin
        randcase
            1 : out = sel[0];
            1 : out = sel[1];
            1 : out = sel[2];
            1 : out = sel[3];
        endcase
    end
    initial begin
        randsequence()
            seq1 : { rs_tmp = sel[0]; };
        endsequence
    end
endmodule
module mod_assert_checker(
    input  logic clk,
    input  logic in_sig,
    output logic out_sig
);
    property p1; @(posedge clk) in_sig; endproperty
    assert property(p1);
    always_ff @(posedge clk) begin
        assert(in_sig) out_sig <= 1'b1; else out_sig <= 1'b0;
    end
    logic tmp_local;
    initial begin
        @(posedge clk);
        tmp_local = in_sig;
        wait(in_sig) tmp_local = 1'b1;
        simple_chk sc_inst(.sig(in_sig));
    end
endmodule
