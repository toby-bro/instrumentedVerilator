`ifndef VERILATOR
`define WITH_COVERAGE
`endif
module option_covergroup_mod #(
    parameter int W = 8
) (
    input  logic                   clk,
    input  logic                   rst_n,
    input  logic [W-1:0]           din,
    output logic                   ready
);
    assign ready = rst_n;
`ifdef WITH_COVERAGE
    covergroup cg_opt @(posedge clk);
        option.name    = "option_covergroup_mod";
        option.weight  = 2;
        option.goal    = 100;
        option.comment = "testing option builder";
        type_option.weight = 5;
        type_option.goal   = 50;
        cp : coverpoint din {
            bins low  = { [0:15]   };
            bins mid  = { [16:127] };
            bins high = { [128:255] };
        }
    endgroup
    cg_opt cg_inst;
    initial begin
        cg_inst = new();
    end
`endif
endmodule
module bins_wild_mod (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [7:0]  sig,
    output logic        done
);
    assign done = ~rst_n;
`ifdef WITH_COVERAGE
    covergroup cg_bins @(posedge clk);
        cp1 : coverpoint sig iff (rst_n) {
            wildcard     bins unknownVals = { 8'hx, 8'hz };
            ignore_bins  upperRange       = { [8'h80:8'hFF] };
            illegal_bins ill_default      = default;
            bins         ranged[]         = { [0:127] } with (item inside { [0:31] });
        }
    endgroup
    cg_bins cg_inst;
    initial begin
        cg_inst = new();
    end
`endif
endmodule
module trans_bins_mod (
    input  logic       clk,
    input  logic [3:0] in_sig,
    output logic       flag
);
    assign flag = in_sig[0];
`ifdef WITH_COVERAGE
    covergroup cg_trans @(posedge clk);
        cp : coverpoint in_sig {
            bins t1 = (1 => 2 => 3);
        }
    endgroup
    cg_trans cg_inst;
    initial begin
        cg_inst = new();
    end
`endif
endmodule
module cross_mod (
    input  logic       clk,
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic       valid
);
    assign valid = |(a & b);
`ifdef WITH_COVERAGE
    covergroup cg_cross @(posedge clk);
        cp_a : coverpoint a;
        cp_b : coverpoint b;
        cross_ab : cross cp_a, cp_b {
            option.cross_num_print_missing = 2;
            type_option.weight = 4;
            bins selectAll = binsof(cp_a) intersect {3} && binsof(cp_b);
        }
    endgroup
    cg_cross cg_inst;
    initial begin
        cg_inst = new();
    end
`endif
endmodule
