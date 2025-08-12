module basic_cover_mod(
    input  logic         clk,
    input  logic [7:0]   sig1,
    input  logic [7:0]   sig2,
    output logic [7:0]   sig_out
);
    assign sig_out = sig1;
`ifndef VERILATOR
    covergroup cg_opt @(posedge clk);
        option.per_instance = 1;
        option.cross_num_print_missing = 1;
        type_option.weight = 2;
        type_option.goal   = 90;
        cp1 : coverpoint sig1 iff (sig1 != 8'h00) {
            bins zero  = {8'h00};
            bins low   = {[8'h01 : 8'h7F]};
            bins high  = {[8'h80 : 8'hFE]};
        }
        cp2 : coverpoint sig2 {
            bins all = {[8'h00 : 8'hFF]};
        }
        cross cp1, cp2;
    endgroup
    cg_opt cg_inst = new;
`endif
endmodule
module cross_filter_mod(
    input  logic        clk,
    input  logic [3:0]  a,
    input  logic [3:0]  b,
    output logic [3:0]  y
);
    assign y = a & b;
`ifndef VERILATOR
    covergroup cg_cross @(posedge clk);
        cp_a : coverpoint a { bins any_a = {[4'h0 : 4'hF]}; }
        cp_b : coverpoint b { bins any_b = {[4'h0 : 4'hF]}; }
        cross cp_a, cp_b {
            option.weight = 2;
        }
    endgroup
    cg_cross cross_handle = new;
`endif
endmodule
module transition_bins_mod(
    input  logic        clk,
    input  logic [1:0]  s,
    output logic [1:0]  so
);
    assign so = s;
`ifndef VERILATOR
    covergroup cg_trans @(posedge clk);
        cp_s : coverpoint s {
            bins t01  = (0 => 1);
            bins t10  = (1 => 0);
            bins seq1 = (0 => 1 => 2);
        }
    endgroup
    cg_trans trans_handle = new;
`endif
endmodule
module class_cover_mod(
    input  logic sig,
    output logic sig_o
);
    assign sig_o = sig;
`ifndef VERILATOR
    class base_c;
        bit ref_sig;
        covergroup cg_base_inst;
            cp : coverpoint ref_sig;
        endgroup
        function new(bit inbound);
            ref_sig = inbound;
            cg_base_inst = new;
        endfunction
    endclass
    class derived_c extends base_c;
        covergroup cg_ext_inst;
            cp_ext : coverpoint ref_sig;
            option.weight = 2;
        endgroup
        function new(bit inbound);
            super.new(inbound);
            cg_ext_inst = new;
        endfunction
    endclass
    derived_c d;
    initial begin
        d = new(sig);
    end
`endif
endmodule
module logical_cover_mod(
    input  logic        clk,
    input  logic [15:0] r_in,
    output logic        dummy
);
    assign dummy = 1'b0;
`ifndef VERILATOR
    covergroup cg_logic @(posedge clk);
        cp_r : coverpoint r_in {
            bins low = {[16'h0000 : 16'h00FF]};
        }
    endgroup
    cg_logic logic_handle = new;
`endif
endmodule
