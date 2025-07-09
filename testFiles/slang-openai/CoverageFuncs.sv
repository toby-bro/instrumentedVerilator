package coverage_dpi;
    import "DPI-C" function int   coverage_control    (input int a, input int b, input int c, input string s);
    import "DPI-C" function int   coverage_get_max    (input int a, input int b, input string s);
    import "DPI-C" function int   coverage_get        (input int a, input int b, input string s);
    import "DPI-C" function int   coverage_merge      (input int a, input string s);
    import "DPI-C" function int   coverage_save       (input int a, input string s);
    import "DPI-C" function real  get_coverage        ();
    import "DPI-C" function void  set_coverage_db_name(input string s);
    import "DPI-C" function void  load_coverage_db    (input string s);
endpackage
module cov_control_mod(
    input  logic        in_sig,
    output logic [31:0] out_sig
);
    import coverage_dpi::*;
    string scope_name;
    always_comb begin
        scope_name = "unit_scope";
        out_sig    = coverage_control(0, 1, 2, scope_name);
    end
endmodule
module cov_get_max_mod(
    input  logic  [3:0] sel,
    output logic [31:0] max_out
);
    import coverage_dpi::*;
    string hier_name;
    always_comb begin
        hier_name = "hier_scope";
        max_out   = coverage_get_max(1, 2, hier_name);
    end
endmodule
module cov_get_mod(
    input  logic  [7:0] data_in,
    output logic [31:0] cov_val
);
    import coverage_dpi::*;
    string hier;
    always_comb begin
        hier    = "another_scope";
        cov_val = coverage_get(2, 3, hier);
    end
endmodule
module cov_merge_mod(
    input  logic  [3:0] a,
    output logic  [3:0] merged
);
    import coverage_dpi::*;
    int res;
    always_comb begin
        res    = coverage_merge(0, "cov_merge.db");
        merged = a ^ res[3:0];
    end
endmodule
module cov_save_mod(
    input  logic  [3:0] a,
    output logic  [3:0] saved
);
    import coverage_dpi::*;
    int res;
    always_comb begin
        res   = coverage_save(0, "cov_save.db");
        saved = a | res[3:0];
    end
endmodule
module get_coverage_mod(
    input  logic        clk,
    output logic [63:0] cov_bits
);
    import coverage_dpi::*;
    real cov;
    always_comb begin
        cov      = get_coverage();
        cov_bits = $realtobits(cov);
    end
endmodule
module set_cov_db_name_mod(
    input  logic trig,
    output logic ack
);
    import coverage_dpi::*;
    always_comb begin
        set_coverage_db_name("coverage_database_name");
        ack = trig;
    end
endmodule
module load_cov_db_mod(
    input  logic trig,
    output logic ack
);
    import coverage_dpi::*;
    always_comb begin
        load_coverage_db("coverage_database_name");
        ack = trig;
    end
endmodule
