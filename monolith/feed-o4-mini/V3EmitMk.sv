module hist_gen #(parameter int MAX_BAR_LENGTH = 80, parameter int MAX_INTERVALS_NUM = 60) (
    input  logic signed [31:0] scores[$],
    output logic signed [31:0] lowerBound       [0:MAX_INTERVALS_NUM-1],
    output logic signed [31:0] intervalCount    [0:MAX_INTERVALS_NUM-1]
);
    logic signed [31:0] sortedScores[$];
    function automatic void sortScores(input logic signed [31:0] inArr[$], output logic signed [31:0] outArr[$]);
        int n; int i; int j;
        outArr = inArr;
        n = outArr.size();
        for (i = 0; i < n; i++) begin
            for (j = i + 1; j < n; j++) begin
                if (outArr[j] < outArr[i]) begin
                    logic signed [31:0] t;
                    t = outArr[i];
                    outArr[i] = outArr[j];
                    outArr[j] = t;
                end
            end
        end
    endfunction
    always_comb begin
        int i; int k; int intervalsNum; int idx;
        logic signed [31:0] topScore;
        for (i = 0; i < MAX_INTERVALS_NUM; i++) begin
            lowerBound[i]    = '0;
            intervalCount[i] = '0;
        end
        if (scores.size() > 0) begin
            sortScores(scores, sortedScores);
            topScore = sortedScores[sortedScores.size()-1];
            intervalsNum = ((topScore + 1) < MAX_INTERVALS_NUM) ? (topScore + 1) : MAX_INTERVALS_NUM;
            for (i = 0; i < intervalsNum; i++) begin
                lowerBound[i] = (i == 0) ? 0 : ((topScore + 1) * i / intervalsNum) + 1;
            end
            for (k = 0; k < sortedScores.size(); k++) begin
                idx = (sortedScores[k] * intervalsNum) / (topScore + 1);
                if (idx < intervalsNum) intervalCount[idx]++;
            end
        end
    end
endmodule
module worklist_build #(
    parameter int MIN_FILES = 4
) (
    input  logic [31:0] fileScores[$],
    output logic [31:0] listTotal     [$],
    output logic        isConcatenate [$]
);
    typedef struct {
        int              id;
        logic [31:0]     totalScore;
        logic            canConcat;
        logic [31:0]     files     [$];
    } WorkList;
    WorkList lists[$];
    always_comb begin
        WorkList w;
        int nextId; int i; int j;
        logic [31:0] sumScores; logic [31:0] threshold; logic conc;
        lists           = {};
        listTotal       = {};
        isConcatenate   = {};
        nextId    = 0;
        sumScores = 0;
        threshold = 0;
        if (fileScores.size() > 0) begin
            for (i = 0; i < fileScores.size(); i++) sumScores += fileScores[i];
            threshold = (sumScores / fileScores.size()) / 2;
        end
        for (i = 0; i < fileScores.size(); i++) begin
            conc = (fileScores[i] <= threshold);
            if (lists.size() == 0 || lists[lists.size()-1].canConcat != conc) begin
                w.id         = nextId;
                w.totalScore = 0;
                w.canConcat  = conc;
                w.files      = {};
                nextId++;
                lists.push_back(w);
            end
            lists[lists.size()-1].files.push_back(fileScores[i]);
            lists[lists.size()-1].totalScore += fileScores[i];
        end
        for (j = 0; j < lists.size(); j++) begin
            listTotal.push_back(lists[j].totalScore);
            isConcatenate.push_back(lists[j].canConcat);
        end
    end
endmodule
module bucket_assign (
    input  logic [31:0] listSizes[$],
    input  int          totalBuckets,
    output logic [31:0] bucketsAssigned[$]
);
    always_comb begin
        int i; int remaining; int n; int assignCount;
        logic [31:0] sumSizes;
        bucketsAssigned = {};
        remaining       = totalBuckets;
        sumSizes        = 0;
        n               = listSizes.size();
        for (i = 0; i < n; i++) sumSizes += listSizes[i];
        for (i = 0; i < n; i++) begin
            if (remaining > 0 && sumSizes != 0)
                assignCount = (listSizes[i] * totalBuckets) / sumSizes;
            else
                assignCount = 0;
            if (assignCount < 1 && remaining > 0) assignCount = 1;
            if (assignCount > remaining) assignCount = remaining;
            bucketsAssigned.push_back(assignCount);
            remaining -= assignCount;
        end
    end
endmodule
module output_builder (
    input  logic [31:0] buckets[$],
    input  logic [31:0] files  [$],
    output logic [31:0] groupId    [$],
    output logic [31:0] groupFiles[$][$]
);
    always_comb begin
        int b; int k; int fid; int cnt;
        logic [31:0] grp[$];
        groupId    = {};
        groupFiles = {};
        fid = 0;
        for (b = 0; b < buckets.size(); b++) begin
            cnt = buckets[b];
            if (cnt > 0) begin
                grp = {};
                for (k = 0; k < cnt && fid < files.size(); k++) begin
                    grp.push_back(files[fid++]);
                end
                groupId.push_back(b);
                groupFiles.push_back(grp);
            end
        end
        if (fid < files.size() && groupFiles.size() > 0) begin
            groupFiles[groupFiles.size()-1].push_back(files[fid]);
        end
    end
endmodule
module assert_files (
    input  string inNames[$],
    input  string outNames[$],
    output logic match
);
    always_comb begin
        int i;
        match = 1;
        if (inNames.size() != outNames.size())
            match = 0;
        else begin
            for (i = 0; i < inNames.size(); i++) begin
                if (inNames[i] != outNames[i])
                    match = 0;
            end
        end
    end
endmodule
module str_build (
    input  string prefix,
    input  int    idx,
    output string name
);
    always_comb begin
        name = $sformatf("%s_grp%d", prefix, idx);
    end
endmodule
module makefile_flags (
    input  string flags[$],
    output string flagLine
);
    always_comb begin
        int i;
        flagLine = "";
        for (i = 0; i < flags.size(); i++) begin
            flagLine = {flagLine, flags[i], " "};
        end
    end
endmodule
module gen_controls (
    input  logic VM_SC,
    input  logic VM_TRACE,
    output logic VM_C11,
    output logic VM_TIMING
);
    always_comb begin
        if (VM_SC) begin
            VM_C11    = 1;
            VM_TIMING = VM_TRACE;
        end else begin
            VM_C11    = 0;
            VM_TIMING = VM_TRACE;
        end
    end
endmodule
module class_usage (
    input  logic       clk,
    input  logic       rst,
    input  logic [7:0] idIn,
    input  logic [7:0] scoreIn,
    output logic       done
);
    class WorkItem;
        rand logic [7:0] id;
        rand logic [7:0] score;
        function new(int iid, int scr);
            id    = iid;
            score = scr;
        endfunction
    endclass
    WorkItem wi;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) done <= 0;
        else begin
            wi   = new(idIn, scoreIn);
            done <= 1;
        end
    end
endmodule
