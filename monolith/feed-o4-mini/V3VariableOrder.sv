module DebugTools(input logic enable, output logic [1:0] level, output logic [1:0] jsonLevel, output logic [1:0] eitherLevel);
    parameter integer LEVEL = 2;
    function logic debug(input logic en); begin return en; end endfunction
    function logic [1:0] dumpTreeLevel(); begin return LEVEL; end endfunction
    function logic [1:0] dumpTreeJsonLevel(); begin return LEVEL * 2; end endfunction
    function logic [1:0] dumpTreeEitherLevel(); begin
        if (enable) return dumpTreeLevel();
        else return dumpTreeJsonLevel();
    end endfunction
    always_comb begin
        if (debug(enable)) begin
            level      = dumpTreeLevel();
            jsonLevel  = dumpTreeJsonLevel();
            eitherLevel= dumpTreeEitherLevel();
        end else begin
            level      = '0;
            jsonLevel  = '0;
            eitherLevel= '0;
        end
    end
endmodule
module GatherAffinity #(parameter integer IDCOUNT = 8)(
    input  logic                  nodeVarRef,
    input  logic                  user1SetOnce,
    input  logic                  basic_isTriggerVec,
    input  logic [$clog2(IDCOUNT)-1:0] var_id,
    output logic [IDCOUNT-1:0]    affinity
);
    always_comb begin
        affinity = '0;
        if (nodeVarRef && !user1SetOnce) begin
            if (!basic_isTriggerVec) begin
                affinity[var_id] = 1'b1;
            end
        end
    end
endmodule
module VarTspSorter #(parameter integer SIZE = 8)(
    input  logic                  clk,
    input  logic                  reset,
    input  logic [SIZE-1:0]       mTaskIds,
    input  logic [SIZE-1:0]       otherTaskIds,
    output logic                  lessThan,
    output integer                costOut
);
    logic [31:0] serial_reg;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) serial_reg <= 0;
        else      serial_reg <= serial_reg + 1;
    end
    integer i;
    always_comb begin
        lessThan = (serial_reg < serial_reg);
        costOut  = 0;
        for (i = 0; i < SIZE; i = i + 1) begin
            costOut = costOut + (mTaskIds[i] ^ otherTaskIds[i]);
        end
    end
endmodule
module VarAttributesCalc #(
    parameter integer MAXV = 16
)(
    input  logic [MAXV-1:0]           isStatic,
    input  logic [MAXV-1:0]           isPrimaryIO,
    input  logic [MAXV-1:0]           isUsedClock,
    input  logic [MAXV-1:0]           basicOpaque,
    input  logic [MAXV-1:0]           isScBv,
    input  logic [MAXV-1:0]           isScBigUint,
    input  logic [31:0]               widthAlignBytes [MAXV],
    output logic [7:0]                stratum [MAXV],
    output logic                      anonOk  [MAXV]
);
    integer idx;
    always_comb begin
        for (idx = 0; idx < MAXV; idx = idx + 1) begin
            if (isPrimaryIO[idx]) stratum[idx] = 8'd0;
            else if (isUsedClock[idx] && widthAlignBytes[idx] == 1) stratum[idx] = 8'd1;
            else if (basicOpaque[idx]) stratum[idx] = 8'd8;
            else if (isScBv[idx] || isScBigUint[idx]) stratum[idx] = 8'd7;
            else if (widthAlignBytes[idx] == 8) stratum[idx] = 8'd6;
            else if (widthAlignBytes[idx] == 4) stratum[idx] = 8'd5;
            else if (widthAlignBytes[idx] == 2) stratum[idx] = 8'd3;
            else if (widthAlignBytes[idx] == 1) stratum[idx] = 8'd2;
            else stratum[idx] = 8'd10;
            anonOk[idx] = !basicOpaque[idx];
        end
    end
endmodule
module VarSimpleSort #(
    parameter integer N = 16
)(
    input  logic [N-1:0]       inStatic,
    input  logic [7:0]         inStratum [N],
    input  logic               inAnonOk  [N],
    output logic [N-1:0]       sortedIdx
);
    integer i, j, tmp;
    integer order [N];
    logic [7:0]   local_stratum [N];
    logic         local_anonOk  [N];
    logic         local_isStatic[N];
    always_comb begin
        for (i = 0; i < N; i = i + 1) begin
            order[i]          = i;
            local_stratum[i]  = inStratum[i];
            local_anonOk[i]   = inAnonOk[i];
            local_isStatic[i] = inStatic[i];
        end
        for (i = 0; i < N-1; i = i + 1) begin
            for (j = 0; j < N-1-i; j = j + 1) begin
                if (local_isStatic[order[j]] != local_isStatic[order[j+1]]) begin
                    if (local_isStatic[order[j]]) begin
                        tmp = order[j]; order[j] = order[j+1]; order[j+1] = tmp;
                    end
                end else if (local_anonOk[order[j]] != local_anonOk[order[j+1]]) begin
                    if (!local_anonOk[order[j]]) begin
                        tmp = order[j]; order[j] = order[j+1]; order[j+1] = tmp;
                    end
                end else if (local_stratum[order[j]] > local_stratum[order[j+1]]) begin
                    tmp = order[j]; order[j] = order[j+1]; order[j+1] = tmp;
                end
            end
        end
        for (i = 0; i < N; i = i + 1) sortedIdx[i] = order[i];
    end
endmodule
module VarTspSort #(
    parameter integer N = 16,
    parameter integer IDCOUNT = 8
)(
    input  logic [IDCOUNT-1:0] mTaskIdsList [N],
    output logic [N-1:0]       sortedIdx
);
    logic [IDCOUNT-1:0] emptyVec;
    logic [IDCOUNT-1:0] uniquesVec [N];
    integer statesCount, count, k, outIdx;
    integer order [N];
    always_comb begin
        emptyVec    = '0;
        statesCount = 0;
        for (count = 0; count < N; count = count + 1) begin
            if (mTaskIdsList[count] != emptyVec) begin
                bit seen = 0;
                for (k = 0; k < statesCount; k = k + 1) begin
                    if (mTaskIdsList[count] == uniquesVec[k]) seen = 1;
                end
                if (!seen) begin
                    uniquesVec[statesCount] = mTaskIdsList[count];
                    statesCount = statesCount + 1;
                end
            end
        end
        outIdx = 0;
        for (count = 0; count < statesCount; count = count + 1) begin
            for (k = 0; k < N; k = k + 1) begin
                if (mTaskIdsList[k] == uniquesVec[count]) begin
                    order[outIdx] = k;
                    outIdx = outIdx + 1;
                end
            end
        end
        for (count = 0; count < N; count = count + 1) begin
            if (mTaskIdsList[count] == emptyVec) begin
                order[outIdx] = count;
                outIdx = outIdx + 1;
            end
        end
        for (count = 0; count < N; count = count + 1) sortedIdx[count] = order[count];
    end
endmodule
module V3VariableOrderProc #(
    parameter integer MODCNT = 4
)(
    input  logic                  opt_mtasks,
    input  logic                  opt_stats,
    input  logic [MODCNT-1:0]     modules_present,
    output logic [MODCNT-1:0]     processed
);
    function void statsStage(input string stage); begin end endfunction
    integer modIdx;
    always_comb begin
        processed = '0;
        if (opt_mtasks) begin
        end
        if (opt_stats) statsStage("variableorder-gather");
        for (modIdx = 0; modIdx < MODCNT; modIdx = modIdx + 1) begin
            if (modules_present[modIdx]) processed[modIdx] = 1'b1;
        end
        if (opt_stats) statsStage("variableorder-sort");
    end
endmodule
