module newOutCFile_mdl(
    input  logic [31:0] count,
    output logic [319:0] fileName
);
    always_comb begin
        unique case (count % 4)
            0: fileName = "dir/topClass__ConstPool_0.cpp";
            1: fileName = "dir/topClass__ConstPool_1.cpp";
            2: fileName = "dir/topClass__ConstPool_2.cpp";
            default: fileName = "dir/topClass__ConstPool_3.cpp";
        endcase
    end
endmodule
module maybeSplitCFile_mdl(
    input  logic [31:0] outputSplit,
    input  logic [31:0] outFileSize,
    input  logic [31:0] oldCount,
    output logic        useParallel,
    output logic [31:0] nextFileSize,
    output logic [31:0] outFileCount
);
    always_comb begin
        if ((outputSplit != 0) && (outFileSize >= outputSplit)) begin
            useParallel   = 1;
            nextFileSize  = 0;
            outFileCount  = oldCount + 1;
        end else begin
            useParallel   = 0;
            nextFileSize  = outFileSize;
            outFileCount  = oldCount;
        end
    end
endmodule
module emitVarsSort2(
    input  logic        go,
    output logic [31:0] out0,
    output logic [31:0] out1,
    output logic [31:0] out2,
    output logic [31:0] out3,
    output logic        done
);
    localparam logic [31:0] arr_init [0:3] = '{32'd4,32'd1,32'd3,32'd2};
    logic [31:0] arr [0:3];
    integer i, j;
    always_comb begin
        for (i = 0; i < 4; i = i + 1)
            arr[i] = arr_init[i];
        if (go) begin
            for (i = 0; i < 4; i = i + 1) begin
                for (j = 0; j < 4 - i - 1; j = j + 1) begin
                    if (arr[j] > arr[j+1]) begin
                        logic [31:0] tmp;
                        tmp      = arr[j];
                        arr[j]   = arr[j+1];
                        arr[j+1] = tmp;
                    end
                end
            end
            done = 1;
        end else begin
            done = 0;
        end
    end
    assign out0 = arr[0];
    assign out1 = arr[1];
    assign out2 = arr[2];
    assign out3 = arr[3];
endmodule
module compareStrings(
    input  logic [8*16:1] strA,
    input  logic [8*16:1] strB,
    output logic         less
);
    function automatic logic cmp_string_less(input logic [8*16:1] a, input logic [8*16:1] b);
        integer idx;
        begin
            cmp_string_less = 0;
            for (idx = 8*16; idx >= 8; idx = idx - 8) begin
                logic [7:0] charA = a[idx -: 8];
                logic [7:0] charB = b[idx -: 8];
                if (charA < charB) begin
                    cmp_string_less = 1;
                    return;
                end else if (charA > charB) begin
                    cmp_string_less = 0;
                    return;
                end
            end
        end
    endfunction
    always_comb less = cmp_string_less(strA, strB);
endmodule
module visitConst_mdl(
    input  logic        isString,
    input  logic        isWide,
    input  logic [31:0] widthWords,
    input  logic [31:0] numBits,
    output logic [31:0] sizeIncrement
);
    always_comb begin
        if (isString)
            sizeIncrement = 10;
        else if (isWide)
            sizeIncrement = widthWords;
        else
            sizeIncrement = 1;
    end
endmodule
module statsAdder_mdl(
    input  logic [63:0] tablesEmitted,
    input  logic [63:0] constsEmitted,
    output logic [63:0] sumTables,
    output logic [63:0] sumConsts
);
    assign sumTables = tablesEmitted + 0;
    assign sumConsts = constsEmitted + 0;
endmodule
module V3EmitC_emitcConstPool_mdl(
    input  logic clk,
    input  logic trigger,
    output logic done
);
    always_ff @(posedge clk) begin
        if (trigger)
            done <= 1;
        else
            done <= 0;
    end
endmodule
