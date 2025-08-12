module protect_basic (
    input  logic in_sig,
    output logic out_sig
);
    assign out_sig = in_sig;
`pragma protect begin
`pragma protect end
endmodule
module protect_protected (
    input  logic in_sig,
    output logic out_sig
);
    assign out_sig = in_sig;
`pragma protect begin_protected
`pragma protect end_protected
endmodule
module protect_encoding_cfg (
    input  logic a,
    output logic b
);
    assign b = a;
`pragma protect encoding=(enctype="base64",line_length=64,bytes=128)
endmodule
module protect_license_cfg (
    input  logic a,
    output logic b
);
    assign b = a;
`pragma protect license=(library="std_lib",entry="encrypt",feature="auth",exit="done",match=32)
endmodule
module protect_viewport_cfg (
    input  logic a,
    output logic b
);
    assign b = a;
`pragma protect viewport=(object="window",access="rw")
endmodule
module pragma_reset_example (
    input  logic a,
    output logic b
);
    assign b = a;
`pragma reset protect
`pragma reset once
`pragma reset diagnostic
endmodule
module pragma_resetall_example (
    input  logic a,
    output logic b
);
    assign b = a;
`pragma resetall
endmodule
module pragma_once_example (
    input  logic a,
    output logic b
);
    assign b = a;
`pragma once
endmodule
module diagnostic_push_pop_example (
    input  logic a,
    output logic b
);
    assign b = a;
`pragma diagnostic push
`pragma diagnostic pop
endmodule
module diagnostic_level_example (
    input  logic a,
    output logic b
);
    assign b = a;
`pragma diagnostic ignore="UNSIGNED_SIG"
`pragma diagnostic warn=("WIDTH_MISMATCH","XPROP_WARNING")
`pragma diagnostic error="DELAY_INFERRED"
endmodule
