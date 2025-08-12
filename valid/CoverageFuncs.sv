module mod_cov_child (input logic in, output logic out);
    assign out = in;
endmodule
module cov_control_str (
    input  logic        dummy_in,
    output logic [31:0] result
);
    assign result = $coverage_control(1, 2, 3, "cov_scope");
endmodule
module cov_control_var (
    input  logic        clk,
    output logic [31:0] result
);
    string scope_id = "cov_scope_var";
    assign result = $coverage_control(4, 5, 6, scope_id);
endmodule
module cov_get_max_mod (
    input  logic        enable,
    output logic [31:0] value
);
    string scopeName = "cov_scope_max";
    assign value = $coverage_get_max(7, 8, scopeName);
endmodule
module cov_get_mod (
    input  logic        enable,
    output logic [31:0] value
);
    string grp = "cov_scope_get";
    assign value = $coverage_get(9, 10, grp);
endmodule
module cov_merge_mod (
    input  logic        trig,
    output logic [31:0] merged
);
    assign merged = $coverage_merge(11, "merge_file");
endmodule
module cov_save_mod (
    input  logic        trig,
    output logic [31:0] saved
);
    assign saved = $coverage_save(12, "save_db");
endmodule
module get_coverage_mod (
    input  logic dummy_in,
    output real  cov_value
);
    assign cov_value = $get_coverage();
endmodule
module cov_db_ops_mod (
    input  logic        dummy_in,
    output logic [31:0] status
);
    always_comb begin
        void'($set_coverage_db_name("coverage_db_name"));
        void'($load_coverage_db("coverage_db_name"));
        status = 32'd0;
    end
endmodule
