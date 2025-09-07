module debug_mod(input  logic       enable,
                 input  logic [7:0] data_in,
                 output logic [7:0] data_out);
  assign data_out = enable ? data_in : 8'b0;
endmodule
module sumit_mod #(int N = 4)
  (input  logic [7:0]   names      [N],
   input  logic          sumit_flags[N],
   input  logic          printit    [N],
   input  logic [31:0]   values      [N],
   output logic [31:0]   combined    [N]);
  always_comb begin
    for (int i = 0; i < N; i++) begin
      combined[i] = values[i];
    end
    for (int i = 1; i < N; i++) begin
      for (int j = 0; j < i; j++) begin
        if (sumit_flags[i] && printit[i] && printit[j]
            && (names[i] == names[j])) begin
          combined[j] = combined[j] + values[i];
        end
      end
    end
  end
endmodule
module stars_mod #(int N = 4)
  (input  logic [7:0]   names   [N],
   input  logic [7:0]   stages  [N],
   input  logic          printit [N],
   input  logic          perf    [N],
   output logic [7:0]    maxWidth,
   output logic [31:0]   starCount,
   output logic [31:0]   perfCount);
  always_comb begin
    maxWidth  = 0;
    starCount = 0;
    perfCount = 0;
    for (int i = 0; i < N; i++) begin
      if ((stages[i] == 8'h2A) && printit[i]) begin
        if (names[i] > maxWidth) maxWidth = names[i];
        if (!perf[i])          starCount++;
      end
    end
    for (int i = 0; i < N; i++) begin
      if ((stages[i] == 8'h2A) && printit[i] && perf[i]) begin
        perfCount++;
      end
    end
  end
endmodule
module stages_mod #(int N = 4, int S = 3)
  (input  logic [7:0]   names      [N],
   input  logic [7:0]   stages     [N],
   input  logic          printit    [N],
   input  logic [7:0]   stage_tags [S],
   output logic [31:0]   stage_map_count [S],
   output logic [31:0]   matrix     [N][S]);
  always_comb begin
    for (int k = 0; k < S; k++) begin
      stage_map_count[k] = 0;
      for (int i = 0; i < N; i++) matrix[i][k] = 0;
    end
    for (int i = 0; i < N; i++) begin
      if (printit[i] && (stages[i] != 8'h2A)) begin
        for (int k = 0; k < S; k++) begin
          if (stages[i] == stage_tags[k]) begin
            matrix[i][k]     = 1;
            stage_map_count[k]++;
          end
        end
      end
    end
  end
endmodule
module getStatSum_mod #(int N = 4)
  (input  logic [7:0]   names      [N],
   input  logic [7:0]   query_name,
   input  logic [31:0]  values      [N],
   output logic [31:0]  sumOut);
  always_comb begin
    sumOut = 0;
    for (int i = 0; i < N; i++)
      if (names[i] == query_name)
        sumOut += values[i];
  end
endmodule
module addStat_mod(input  logic       enable,
                   input  logic [7:0] new_name,
                   input  logic [31:0] new_value,
                   output logic [7:0] added_name,
                   output logic [31:0] added_value);
  assign added_name  = enable ? new_name   : 8'b0;
  assign added_value = enable ? new_value  : 32'b0;
endmodule
module statsStage_mod(input  logic [31:0] wallTimeNow,
                      input  logic [31:0] lastWallTimeIn,
                      input  logic [47:0] memPeakBytes,
                      input  logic [47:0] memCurrentBytes,
                      output logic [31:0] wallTimeDelta,
                      output logic [31:0] newLastWallTime,
                      output logic [31:0] memPeakMB,
                      output logic [31:0] memCurrentMB);
  always_comb begin
    wallTimeDelta   = wallTimeNow - ((lastWallTimeIn == 0) ? wallTimeNow : lastWallTimeIn);
    newLastWallTime = wallTimeNow;
    memPeakMB       = memPeakBytes    / 1024 / 1024;
    memCurrentMB    = memCurrentBytes / 1024 / 1024;
  end
endmodule
module infoHeader_mod(input  logic [15:0] version,
                      input  logic [31:0] allArgsHash,
                      input  logic [7:0]  buildJobs,
                      input  logic [7:0]  verilateJobs,
                      output logic [31:0] infoCode);
  assign infoCode = version ^ allArgsHash[15:0] ^ buildJobs ^ verilateJobs;
endmodule
module summaryReport_mod(input  logic [31:0] srcCharsMB,
                         input  logic [31:0] srcModules,
                         input  logic [31:0] cppCharsMB,
                         input  logic [31:0] cppFiles,
                         input  logic [31:0] modelMB,
                         input  logic [31:0] walltime,
                         input  logic [31:0] walltimeElab,
                         input  logic [31:0] walltimeCvt,
                         input  logic [31:0] walltimeBuild,
                         input  logic [31:0] cputime,
                         input  logic [7:0]  threads,
                         input  logic [47:0] memPeakBytes,
                         output logic [31:0] memoryMB,
                         output logic [63:0] summaryCode);
  always_comb begin
    memoryMB    = memPeakBytes / 1024 / 1024;
    summaryCode = srcCharsMB + srcModules + cppCharsMB
                + cppFiles  + modelMB    + walltime
                + walltimeElab + walltimeCvt + walltimeBuild
                + cputime  + threads     + memoryMB;
  end
endmodule
module dump_mod(input  logic [31:0] value,
                input  logic [7:0]  precision,
                output logic [31:0] formatted);
  always_comb formatted = value;
endmodule
