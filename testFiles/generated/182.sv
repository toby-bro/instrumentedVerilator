module snippet (
    input wire clk,
    input int inj_config_data_in_1755007814201_177,
    input wire reset,
    output int inj_config_data_out_1755007814201_211
);
    // BEGIN: PragmaProtectOptions_ts1755007814201
`ifdef SLANG_PRAGMA
`protect encoding (enctype="base64", line_length=76, bytes=1024)
`endif
`ifdef SLANG_PRAGMA
`protect license (library="my_project_lib", entry="start_feature_A", match=42, feature="feature_set_B", exit="end_feature_A")
`endif
`ifdef SLANG_PRAGMA
`protect reset
`endif
`ifdef SLANG_PRAGMA
`protect viewport (object="design.module_a.instance_b.register_c", access="read-only")
`endif
assign inj_config_data_out_1755007814201_211 = inj_config_data_in_1755007814201_177 + 1;
    // END: PragmaProtectOptions_ts1755007814201
endmodule

