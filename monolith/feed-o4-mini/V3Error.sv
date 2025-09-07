package V3ErrorPkg;
  typedef enum logic [2:0] { EC_MIN=0, EC_ERROR=1, EC_FATAL=2, EC_FATALMANY=3, EC_FATALSRC=4, EC_FIRST_NAMED=5, EC_ENUM_MAX=6 } error_code_t;
  function int debug(); return 0; endfunction
  function int dumpTreeLevel(); return 1; endfunction
  function int dumpTreeJsonLevel(); return 2; endfunction
  class V3ErrorCode;
    error_code_t m_e;
    function new(string msgp); m_e = EC_ERROR; endfunction
    function error_code_t code(); return m_e; endfunction
    function string ascii(); return "EC_ERROR"; endfunction
    function string url(); return {"https://verilator.org/warn/", ascii()}; endfunction
    function bit hardError(); return (m_e == EC_FATAL); endfunction
    function bit severityInfo(); return (m_e == EC_ERROR); endfunction
  endclass
  class V3ErrorGuarded;
    V3ErrorCode m_message;
    bit m_errorSuppressed;
    function bit isError(V3ErrorPkg::V3ErrorCode code, bit supp);
      if (code.hardError()) return 1;
      if (supp) return 0;
      if (code.severityInfo()) return 0;
      return 0;
    endfunction
    function string msgPrefix(); return {"%Error: ", m_message.ascii()}; endfunction
    function int warnMoreSpaces(); return msgPrefix().len(); endfunction
    function bit suppressThisWarning(); m_errorSuppressed = 1; return m_errorSuppressed; endfunction
    function error_code_t v3errorPrep(error_code_t code); m_message = new("prep"); return code; endfunction
    function bit v3errorEnd(); return 1; endfunction
    function bit v3errorEndGuts(); return 1; endfunction
    function bit vlAbortOrExit(); return 1; endfunction
  endclass
  class V3Error;
    static function bit init(); return 1; endfunction
    static function string lineStr(string filename, int lineno); return $sformatf("%s:%0d:", filename, lineno); endfunction
    static function string stripMetaText(string text, bit stripContext); return text; endfunction
    static function bit abortIfWarnings(); return 0; endfunction
    static function int vlAbort(); return 0; endfunction
    static function bit v3errorPrep(error_code_t code); return 1; endfunction
    static function string v3errorPrepFileLine(error_code_t code, string file, int line); return ""; endfunction
    static function bit v3errorEndFunc(error_code_t code, string sstr, string extra); return 1; endfunction
  endclass
  function bit v3errorEndGlobal(string sstr); return 1; endfunction
  function bit v3errorEndFatalGlobal(string sstr); return 1; endfunction
endpackage
module m_debug(input logic en, output logic [31:0] out);
  import V3ErrorPkg::*;
  always_comb begin
    out = en ? debug() : 0;
  end
endmodule
module m_dumpTreeLevel(input logic en, output logic [31:0] out);
  import V3ErrorPkg::*;
  always_comb begin
    out = en ? dumpTreeLevel() : 0;
  end
endmodule
module m_dumpTreeJsonLevel(input logic en, output logic [31:0] out);
  import V3ErrorPkg::*;
  always_comb begin
    out = en ? dumpTreeJsonLevel() : 0;
  end
endmodule
module m_V3ErrorCodeCtor(input logic en, output logic [2:0] out);
  import V3ErrorPkg::*;
  always_comb begin
    static V3ErrorCode c = new("msg");
    out = en ? c.code() : EC_MIN;
  end
endmodule
module m_V3ErrorCodeUrl(input logic en, output logic [31:0] out);
  import V3ErrorPkg::*;
  always_comb begin
    static V3ErrorCode c = new("msg");
    out = en ? c.url().len() : 0;
  end
endmodule
module m_isError(input logic en, output logic out);
  import V3ErrorPkg::*;
  always_comb begin
    static V3ErrorGuarded g = new();
    static V3ErrorCode c = new("msg");
    out = en ? g.isError(c, en) : 0;
  end
endmodule
module m_msgPrefix(input logic en, output logic [31:0] out);
  import V3ErrorPkg::*;
  always_comb begin
    static V3ErrorGuarded g = new();
    out = en ? g.msgPrefix().len() : 0;
  end
endmodule
module m_vlAbortOrExit(input logic en, output logic out);
  import V3ErrorPkg::*;
  always_comb begin
    static V3ErrorGuarded g = new();
    out = en ? g.vlAbortOrExit() : 0;
  end
endmodule
module m_warnMoreSpaces(input logic en, output logic [31:0] out);
  import V3ErrorPkg::*;
  always_comb begin
    static V3ErrorGuarded g = new();
    if (en) g.v3errorPrep(EC_ERROR);
    out = en ? g.warnMoreSpaces() : 0;
  end
endmodule
module m_suppressThisWarning(input logic en, output logic out);
  import V3ErrorPkg::*;
  always_comb begin
    static V3ErrorGuarded g = new();
    out = en ? g.suppressThisWarning() : 0;
  end
endmodule
module m_v3errorPrepG(input logic en, output logic [2:0] out);
  import V3ErrorPkg::*;
  always_comb begin
    static V3ErrorGuarded g = new();
    out = en ? g.v3errorPrep(EC_ERROR) : EC_MIN;
  end
endmodule
module m_v3errorEndG(input logic en, output logic out);
  import V3ErrorPkg::*;
  always_comb begin
    static V3ErrorGuarded g = new();
    out = en ? g.v3errorEnd() : 0;
  end
endmodule
module m_v3errorEndGuts(input logic en, output logic out);
  import V3ErrorPkg::*;
  always_comb begin
    static V3ErrorGuarded g = new();
    out = en ? g.v3errorEndGuts() : 0;
  end
endmodule
module m_init(input logic en, output logic out);
  import V3ErrorPkg::*;
  always_comb begin
    out = en ? V3Error::init() : 0;
  end
endmodule
module m_lineStr(input logic en, input int lineno, output logic [31:0] out);
  import V3ErrorPkg::*;
  always_comb begin
    out = en ? V3Error::lineStr("file.sv", lineno).len() : 0;
  end
endmodule
module m_stripMetaText(input logic en, output logic [31:0] out);
  import V3ErrorPkg::*;
  always_comb begin
    out = en ? V3Error::stripMetaText("text", en).len() : 0;
  end
endmodule
module m_abortIfWarnings(input logic en, output logic out);
  import V3ErrorPkg::*;
  always_comb begin
    out = en ? V3Error::abortIfWarnings() : 0;
  end
endmodule
module m_vlAbort(input logic en, output logic [31:0] out);
  import V3ErrorPkg::*;
  always_comb begin
    out = en ? V3Error::vlAbort() : 0;
  end
endmodule
module m_v3errorPrepE(input logic [2:0] code, output logic out);
  import V3ErrorPkg::*;
  always_comb begin
    out = code != EC_ENUM_MAX ? V3Error::v3errorPrep(error_code_t'(code)) : 0;
  end
endmodule
module m_v3errorPrepFileLine(input logic [2:0] code, input int line, output logic [31:0] out);
  import V3ErrorPkg::*;
  always_comb begin
    out = (code != EC_ENUM_MAX) ? V3Error::v3errorPrepFileLine(error_code_t'(code), "file.sv", line).len() : 0;
  end
endmodule
module m_v3errorEndE(input logic en, output logic out);
  import V3ErrorPkg::*;
  always_comb begin
    out = en ? V3Error::v3errorEndFunc(EC_ERROR, "str", "extra") : 0;
  end
endmodule
module m_v3errorEndGlobal(input logic en, output logic out);
  import V3ErrorPkg::*;
  always_comb begin
    out = en ? v3errorEndGlobal("str") : 0;
  end
endmodule
module m_v3errorEndFatal(input logic en, output logic out);
  import V3ErrorPkg::*;
  always_comb begin
    out = en ? v3errorEndFatalGlobal("str") : 0;
  end
endmodule
