//===========================================================
package helper_pkg;
  class helper_class;
    bit dummy;
    function void flip(); dummy = ~dummy; endfunction
  endclass
endpackage
//===========================================================
module m_escaped_literals (
    input  logic in_sig,
    output logic out_sig
);
    import helper_pkg::*;
    parameter string ESC_STR = "Line1\nLine2\t\v\r\f\a\x41\101\\\"%%";
    string captured;
    always_comb begin
        helper_class c = new();
        captured = ESC_STR;
        out_sig  = in_sig;
    end
endmodule
//===========================================================
module m_long_identifier (
    input  logic in_bus,
    output logic out_bus
);
    import helper_pkg::*;
    logic very_long_identifier_name_that_is_definitely_long_enough_to_exceed_typical_tool_limits_and_thus_should_be_hashed_by_verilator_to_keep_internal_symbol_names_reasonable_________________________________________________________0123456789________________________________________________________ABCDEFGHIJKLMNOPQRSTUVWXYZ________________________________________________________abcdefghijklmnopqrstuvwxyz;
    always_comb begin
        helper_class c = new();
        very_long_identifier_name_that_is_definitely_long_enough_to_exceed_typical_tool_limits_and_thus_should_be_hashed_by_verilator_to_keep_internal_symbol_names_reasonable_________________________________________________________0123456789________________________________________________________ABCDEFGHIJKLMNOPQRSTUVWXYZ________________________________________________________abcdefghijklmnopqrstuvwxyz = in_bus;
        out_bus = very_long_identifier_name_that_is_definitely_long_enough_to_exceed_typical_tool_limits_and_thus_should_be_hashed_by_verilator_to_keep_internal_symbol_names_reasonable_________________________________________________________0123456789________________________________________________________ABCDEFGHIJKLMNOPQRSTUVWXYZ________________________________________________________abcdefghijklmnopqrstuvwxyz;
    end
endmodule
//===========================================================
module m_path_escape (
    input  logic i_path,
    output logic o_path
);
    import helper_pkg::*;
    parameter string PTH = "C:\\Program Files\\Verilator Test\\demo";
    int path_len;
    always_comb begin
        helper_class c = new();
        path_len = PTH.len();
        o_path   = i_path;
    end
endmodule
//===========================================================
module m_real_underscore (
    input  logic i_real,
    output logic o_real
);
    import helper_pkg::*;
    localparam real RNUM = 1_234.567_890;
    real value;
    always_comb begin
        helper_class c = new();
        value = RNUM;
        o_real = i_real;
    end
endmodule
//===========================================================
module m_percent_format (
    input  logic i_fmt,
    output logic o_fmt
);
    import helper_pkg::*;
    string formatted;
    always_comb begin
        helper_class c = new();
        formatted = $sformatf("Value is %%d, input = %0b", i_fmt);
        o_fmt = i_fmt;
    end
endmodule
//===========================================================
module m_case_mix (
    input  logic i_case,
    output logic o_case
);
    import helper_pkg::*;
    typedef enum logic [1:0] {StATE_IdLE, StATE_RUN, sTaTE_DONE} state_t;
    state_t curr_state;
    always_comb begin
        helper_class c = new();
        curr_state = (i_case) ? StATE_RUN : StATE_IdLE;
        o_case     = (curr_state == StATE_RUN);
    end
endmodule
//===========================================================
module m_whitespace_ops (
    input  logic i_ws,
    output logic o_ws
);
    import helper_pkg::*;
    parameter string RAW_TEXT = "   Verilator   \n   Test   ";
    string processed;
    always_comb begin
        helper_class c = new();
        processed = RAW_TEXT;
        o_ws      = i_ws;
    end
endmodule
//===========================================================
module m_wildcard_strings (
    input  logic i_wc,
    output logic o_wc
);
    import helper_pkg::*;
    parameter string PATTERN_A = "*abc?def*";
    parameter string PATTERN_B = "file_??.sv";
    string hold;
    always_comb begin
        helper_class c = new();
        hold = {PATTERN_A, "|", PATTERN_B};
        o_wc = i_wc;
    end
endmodule
