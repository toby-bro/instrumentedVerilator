module mod_boot(input logic clk, input logic rst, output logic done);
  class V3G;
    bit m_hasBoot;
    function void boot(); begin m_hasBoot = 1; end endfunction
  endclass
  V3G glb;
  initial glb = new;
  always_ff @(posedge clk) if (rst) glb.boot();
  always_comb done = glb.m_hasBoot;
endmodule
module mod_shutdown(input logic clk, input logic rst, output logic cleared);
  class V3G2;
    bit m_cleaned;
    function void shutdown(); begin m_cleaned = 1; end endfunction
  endclass
  V3G2 glb;
  initial glb = new;
  always_ff @(posedge clk) if (rst) glb.shutdown();
  always_comb cleared = glb.m_cleaned;
endmodule
module mod_checkTree(input logic trigger, output logic ok);
  class V3G3;
    bit m_ok;
    function void checkTree(); begin m_ok = 1; end endfunction
  endclass
  V3G3 glb;
  initial glb = new;
  always_comb if (trigger) glb.checkTree();
  always_comb ok = glb.m_ok;
endmodule
module mod_readFiles(input logic start, input string files[], output int countParsed);
  class Parser;
    function void parseFile(string fname, string lib, bit flag); endfunction
  endclass
  class V3G4;
    Parser parser;
    function int readFiles(string f[]); int i; begin parser = new; readFiles = 0; for (i = 0; i < f.size(); i++) begin parser.parseFile(f[i], "work", 0); readFiles++; end end endfunction
  endclass
  V3G4 glb;
  initial glb = new;
  always_comb countParsed = start ? glb.readFiles(files) : 0;
endmodule
module mod_removeStd(input logic cond, input string stdName, output logic removed);
  class V3G5;
    bit removedFlag;
    function void removeStd(bit usesStd, string pkg); begin if (!usesStd) removedFlag = 1; end endfunction
  endclass
  V3G5 glb;
  initial glb = new;
  always_comb if (cond) glb.removeStd(1, stdName);
  always_comb removed = glb.removedFlag;
endmodule
module mod_debugFilename(input string nameComment, input int newNumber, output string result);
  class V3G6;
    int m_debugFileNumber;
    function string debugFilename(string nameComment, int newNumber);
      begin
        if (newNumber) m_debugFileNumber = newNumber;
        else m_debugFileNumber++;
        debugFilename = {"/dir/", nameComment, "_", $sformatf("%0d", m_debugFileNumber)};
      end
    endfunction
  endclass
  V3G6 glb;
  initial glb = new;
  always_comb result = glb.debugFilename(nameComment, newNumber);
endmodule
module mod_digitsFilename(input int number, output string digits);
  class V3G7;
    function string digitsFilename(int number);
      begin digitsFilename = $sformatf("%03d", number); end
    endfunction
  endclass
  V3G7 glb;
  initial glb = new;
  always_comb digits = glb.digitsFilename(number);
endmodule
module mod_dumpCheckGlobalTree(
  input logic level,
  input logic jsonLevel,
  input logic doDump,
  input logic dot,
  input logic stats,
  input logic emitV,
  input logic debugCheck,
  output logic checked,
  output logic brokenDone
);
  class V3G8;
    bit checked; bit brokenDone;
    function void dumpCheckGlobalTree(
      bit dumpLevel,
      bit dumpJson,
      bit doDump,
      bit dumpDot,
      bit statsEn,
      bit emitVEn,
      bit debugCheckEn
    );
      begin
        if (dumpLevel) ;
        if (dumpJson) ;
        if (dumpDot) ;
        if (statsEn) ;
        if (emitVEn && doDump) ;
        if (debugCheckEn || dumpLevel) begin checked = 1; brokenDone = 1; end
      end
    endfunction
  endclass
  V3G8 glb;
  initial glb = new;
  always_comb glb.dumpCheckGlobalTree(level, jsonLevel, doDump, dot, stats, emitV, debugCheck);
  always_comb begin checked = glb.checked; brokenDone = glb.brokenDone; end
endmodule
module mod_idPtrMapDumpJson(input logic enable, output string jsonOut);
  class V3G9;
    string m_ptrToId[int];
    function void add(int addr, string id); begin m_ptrToId[addr] = id; end endfunction
    function string dumpJson();
      string out; string sep; int addr;
      begin
        out = "\"pointers\": {";
        sep = "\n  ";
        foreach (m_ptrToId[addr]) begin
          out = {out, sep, "\"", m_ptrToId[addr], "\": \"", $sformatf("%0h", addr), "\""};
          sep = ",\n  ";
        end
        out = {out, "\n }"};
        return out;
      end
    endfunction
  endclass
  V3G9 glb;
  initial begin glb = new; glb.add(32, "A"); glb.add(48, "B"); end
  always_comb jsonOut = enable ? glb.dumpJson() : "";
endmodule
module mod_saveJsonPtrFieldName(input logic enable, input string fieldName, output logic saved);
  class V3G10;
    bit savedFlag; string m_fields[string];
    function void saveName(string name); begin m_fields[name] = ""; savedFlag = 1; end endfunction
  endclass
  V3G10 glb;
  initial glb = new;
  always_comb if (enable) glb.saveName(fieldName);
  always_comb saved = glb.savedFlag;
endmodule
module mod_ptrNamesDumpJson(input logic enable, output string jsonList);
  class V3G11;
    string m_names[string];
    function void addName(string name); begin m_names[name] = ""; end endfunction
    function string dumpNames();
      string out; string sep; string nm;
      begin
        out = "\"ptrFieldNames\": [";
        sep = "\n  ";
        foreach (m_names[nm]) begin
          out = {out, sep, "\"", nm, "\""};
          sep = ",\n  ";
        end
        out = {out, "\n ]"};
        return out;
      end
    endfunction
  endclass
  V3G11 glb;
  initial begin glb = new; glb.addName("f1"); glb.addName("f2"); end
  always_comb jsonList = enable ? glb.dumpNames() : "";
endmodule
module mod_ptrToId(input int ptr, output string idStr);
  class V3G12;
    string letters = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    int m_count = 0;
    function string ptrToId(int p);
      string os; int id;
      begin
        if (p != 0) begin
          m_count++; id = m_count; os = "(";
          do begin os = {os, letters[id % 26]}; id = id / 26; end while (id);
          os = {os, ")"};
        end else os = "0";
        return os;
      end
    endfunction
  endclass
  V3G12 glb;
  initial glb = new;
  always_comb idStr = glb.ptrToId(ptr);
endmodule
module mod_verilatedCppFiles(
  input logic dpi,
  input logic vpi,
  input logic savable,
  input logic coverage,
  input logic trace,
  input string traceBase,
  input logic probDist,
  input logic timing,
  input logic random,
  input logic profiler,
  output string files[]
);
  class V3G13;
    function string[] filesList(
      bit dpiEn, bit vpiEn, bit savableEn, bit covEn,
      bit traceEn, string traceB,
      bit probEn, bit timeEn, bit randEn, bit profEn
    );
      string result[$];
      begin
        result.push_back("verilated.cpp");
        if (dpiEn)       result.push_back("verilated_dpi.cpp");
        if (vpiEn)       result.push_back("verilated_vpi.cpp");
        if (savableEn)   result.push_back("verilated_save.cpp");
        if (covEn)       result.push_back("verilated_cov.cpp");
        if (traceEn)     result.push_back({traceB, "_c.cpp"});
        if (probEn)      result.push_back("verilated_probdist.cpp");
        if (timeEn)      result.push_back("verilated_timing.cpp");
        if (randEn)      result.push_back("verilated_random.cpp");
        result.push_back("verilated_threads.cpp");
        if (profEn)      result.push_back("verilated_profiler.cpp");
        return result;
      end
    endfunction
  endclass
  V3G13 glb;
  initial glb = new;
  always_comb files = glb.filesList(dpi, vpi, savable, coverage, trace, traceBase, probDist, timing, random, profiler);
endmodule
