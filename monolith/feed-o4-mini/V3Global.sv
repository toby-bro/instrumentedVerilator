package V3GlobalPkg;
class AstNetlist;
  function new(); endfunction
  function void deleteTree(); endfunction
  function void checkTree(); endfunction
  function void dumpTreeFile(string fname, bit doDump); endfunction
  function void dumpTreeJsonFile(string fname, bit doDump); endfunction
  function void dumpTreeDotFile(string fname, bit doDump); endfunction
  function AstNetlist unlinkFrBack(); endfunction
endclass
class FileLine;
  function new(string fn); endfunction
  static function string commandLineFilename(); endfunction
endclass
class VInFilter;
  function new(bit pf); endfunction
endclass
class V3Parse;
  function new(AstNetlist r, VInFilter f); endfunction
  function void parseFile(FileLine fl, string fn, bit flag, string lib, string errmsg); endfunction
endclass
class V3LinkCells;
  static function void link(AstNetlist r, VInFilter f); endfunction
endclass
class V3Error;
  static function void abortIfErrors(); endfunction
endclass
class V3Stats;
  static function void statsStage(string s); endfunction
endclass
class V3EmitV;
  static function void debugEmitV(string f); endfunction
endclass
class V3Broken;
  static function void brokenAll(AstNetlist r); endfunction
endclass
endpackage
module BootShutdownMod(input logic clk, input logic rst_n, output logic initialized);
  import V3GlobalPkg::*;
  AstNetlist rootp;
  AstNetlist hierPlanp;
  AstNetlist threadPoolp;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      rootp = null;
      hierPlanp = null;
      threadPoolp = null;
      initialized = 1'b0;
    end else begin
      rootp = new();
      hierPlanp = new();
      threadPoolp = new();
      initialized = 1'b1;
    end
  end
endmodule
module ShutdownMod(input logic shutdown, output logic cleaned);
  import V3GlobalPkg::*;
  AstNetlist rootp;
  AstNetlist hierPlanp;
  AstNetlist threadPoolp;
  always_comb begin
    cleaned = 1'b0;
    if (shutdown) begin
      hierPlanp.deleteTree();
      hierPlanp = null;
      threadPoolp.deleteTree();
      threadPoolp = null;
      rootp.deleteTree();
      rootp = null;
      cleaned = 1'b1;
    end
  end
endmodule
module CheckTreeMod(input logic en, output logic ok);
  import V3GlobalPkg::*;
  AstNetlist rootp;
  always_comb begin
    ok = 1'b0;
    if (en) begin
      rootp = new();
      rootp.checkTree();
      ok = 1'b1;
    end
  end
endmodule
module ReadFilesMod(
  input logic start,
  input logic stdWaiver,
  input logic stdPackage,
  input int vltCount,
  input int vFilesCount,
  input int libraryCount,
  input int hierParamCount,
  output int parsedCount
);
  import V3GlobalPkg::*;
  AstNetlist rootp;
  VInFilter filter;
  V3Parse parser;
  FileLine fl;
  always_comb begin
    int i;
    parsedCount = 0;
    if (start) begin
      rootp = new();
      filter = new(vltCount != 0);
      parser = new(rootp, filter);
      if (stdWaiver) begin
        fl = new("stdWaiver.vlt");
        parser.parseFile(fl, "stdWaiver.vlt", 1'b0, "work", "");
        parsedCount++;
      end
      for (i = 0; i < vltCount; i++) begin
        fl = new("file.vlt");
        parser.parseFile(fl, {"file", $sformatf("%0d", i)}, 1'b0, "lib", "");
        parsedCount++;
      end
      if (stdPackage) begin
        fl = new("stdPkg.sv");
        parser.parseFile(fl, "stdPkg.sv", 1'b0, "work", "");
        parsedCount++;
      end
      for (i = 0; i < vFilesCount; i++) begin
        fl = new("mod.v");
        parser.parseFile(fl, {"mod", $sformatf("%0d", i)}, 1'b0, "lib", "");
        parsedCount++;
      end
      for (i = 0; i < libraryCount; i++) begin
        fl = new("lib.v");
        parser.parseFile(fl, {"lib", $sformatf("%0d", i)}, 1'b1, "lib", "");
        parsedCount++;
      end
      for (i = 0; i < hierParamCount; i++) begin
        fl = new("param.v");
        parser.parseFile(fl, {"param", $sformatf("%0d", i)}, 1'b0, "lib", "");
        parsedCount++;
      end
      V3Error::abortIfErrors();
      V3LinkCells::link(rootp, filter);
      rootp.checkTree();
      V3Broken::brokenAll(rootp);
    end
  end
endmodule
module DebugFilenameMod(input logic trigger, input int newNum, output string filename);
  static int debugNum;
  always_comb begin
    if (trigger) begin
      if (newNum != 0)
        debugNum = newNum;
      else
        debugNum = debugNum + 1;
      filename = {"dir/", "prefix_", $sformatf("%03d", debugNum), "_comment"};
    end else begin
      filename = "";
    end
  end
endmodule
module DigitsFilenameMod(input int number, output string digits);
  always_comb begin
    digits = $sformatf("%03d", number);
  end
endmodule
module DumpCheckGlobalTreeMod(
  input logic trigger,
  input logic dumpTreeLevel,
  input logic dumpTreeJsonLevel,
  input logic dumpTreeDot,
  input logic statsOpt,
  input logic debugEmitVOpt,
  input logic debugCheckOpt,
  input logic dumpTreeEitherLevelOpt,
  output logic done
);
  import V3GlobalPkg::*;
  AstNetlist rootp;
  static int newNumber;
  string treeFilename;
  always_comb begin
    done = 1'b0;
    if (trigger) begin
      newNumber = newNumber + 1;
      treeFilename = {"stage_", $sformatf("%03d", newNumber), ".tree"};
      if (dumpTreeLevel) rootp.dumpTreeFile(treeFilename, 1'b0);
      if (dumpTreeJsonLevel) rootp.dumpTreeJsonFile({treeFilename, ".json"}, 1'b0);
      if (dumpTreeDot) rootp.dumpTreeDotFile({treeFilename, ".dot"}, 1'b0);
      if (statsOpt) V3Stats::statsStage("stage");
      if (debugEmitVOpt) V3EmitV::debugEmitV({treeFilename, ".v"});
      if (debugCheckOpt || dumpTreeEitherLevelOpt) begin
        rootp.checkTree();
        V3Broken::brokenAll(rootp);
      end
      done = 1'b1;
    end
  end
endmodule
module PtrToIdMod(input logic trigger, input bit [31:0] p, output string id);
  string mapping[string];
  always_comb begin
    id = "";
    if (trigger) begin
      if (p == 0) begin
        id = "0";
      end else begin
        int val;
        string tmp;
        string letter;
        val = mapping.num() + 1;
        tmp = "";
        do begin
          letter = $sformatf("%c", 8'h41 + (val % 26));
          tmp = {tmp, letter};
          val = val / 26;
        end while (val != 0);
        id = { "(", tmp, ")" };
      end
      mapping[$sformatf("%0h", p)] = id;
    end
  end
endmodule
module VerilatedCppFilesMod(
  input logic trigger,
  input logic dpi,
  input logic vpi,
  input logic savable,
  input logic coverage,
  input logic trace,
  input string traceSourceBase,
  input logic probDist,
  input logic timing,
  input logic randomize,
  input logic profiler,
  output string files[$]
);
  always_comb begin
    files = {};
    if (trigger) begin
      files.push_back("verilated.cpp");
      if (dpi) files.push_back("verilated_dpi.cpp");
      if (vpi) files.push_back("verilated_vpi.cpp");
      if (savable) files.push_back("verilated_save.cpp");
      if (coverage) files.push_back("verilated_cov.cpp");
      if (trace) files.push_back({traceSourceBase, "_c.cpp"});
      if (probDist) files.push_back("verilated_probdist.cpp");
      if (timing) files.push_back("verilated_timing.cpp");
      if (randomize) files.push_back("verilated_random.cpp");
      files.push_back("verilated_threads.cpp");
      if (profiler) files.push_back("verilated_profiler.cpp");
    end
  end
endmodule
module IdPtrMapDumpJsonMod(input logic trigger, output string jsonOut);
  string mapping[string];
  always_comb begin
    if (trigger) begin
      string sep;
      jsonOut = "\"pointers\": {";
      sep = "\n  ";
      foreach (mapping[idx]) begin
        jsonOut = {jsonOut, sep, "\"", mapping[idx], "\":\"", idx, "\""};
        sep = ",\n  ";
      end
      jsonOut = {jsonOut, "\n }"};
    end else begin
      jsonOut = "";
    end
  end
endmodule
module SaveJsonPtrFieldNameMod(input logic trigger, input string fieldName, output string jsonOut);
  string fieldNames[$];
  always_comb begin
    if (trigger) begin
      string sep;
      jsonOut = "\"ptrFieldNames\": [";
      fieldNames.push_back(fieldName);
      sep = "\n  ";
      foreach (fieldNames[i]) begin
        jsonOut = {jsonOut, sep, "\"", fieldNames[i], "\""};
        sep = ",\n  ";
      end
      jsonOut = {jsonOut, "\n ]"};
    end else begin
      jsonOut = "";
    end
  end
endmodule
