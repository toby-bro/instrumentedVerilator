module seq_split (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [7:0]  data_in,
    output logic [7:0]  out1
);
    (* isolate_assignments *) logic [7:0] iso_seq;
    logic [7:0] aux_seq;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            iso_seq <= '0;
            aux_seq <= '0;
        end else begin
            iso_seq <= data_in;          
            aux_seq <= iso_seq + data_in;
        end
    end
    assign out1 = aux_seq;
endmodule
module comb_split (
    input  logic [15:0] inA,
    input  logic [15:0] inB,
    output logic [15:0] outC
);
    (* isolate_assignments *) logic [15:0] iso_comb;
    logic [15:0] other_comb;
    always_comb begin
        iso_comb   = inA & inB;          
        other_comb = inA | inB;
    end
    assign outC = iso_comb ^ other_comb;
endmodule
module task_call_split (
    input  logic       clk,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    (* isolate_assignments *) logic [7:0] iso_task;
    logic [7:0] mirror_task;
    task automatic inc(ref logic [7:0] x);
        x = x + 8'h1;
    endtask
    always_ff @(posedge clk) begin
        inc(iso_task);                   
        mirror_task <= iso_task;
    end
    assign dout = mirror_task;
endmodule
module nested_split (
    input  logic       clk,
    input  logic       sel,
    input  logic [3:0] din,
    output logic [3:0] y
);
    (* isolate_assignments *) logic [3:0] iso_nested;
    logic [3:0] other_nested;
    always_ff @(posedge clk) begin
        if (sel) begin
            if (din[0]) begin
                iso_nested <= din + 1;   
                other_nested <= '0;
            end else begin
                other_nested <= din;
            end
        end else begin
            iso_nested   <= 4'hF;
            other_nested <= 4'h0;
        end
    end
    assign y = iso_nested & other_nested;
endmodule
module multiblock_split (
    input  logic       clk,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    (* isolate_assignments *) logic [7:0] iso_multi;
    logic [7:0] temp_multi;
    logic [7:0] acc_multi;
    always_ff @(posedge clk) begin
        iso_multi  <= din;               
        temp_multi <= iso_multi + 1;
    end
    always_ff @(posedge clk) begin
        acc_multi <= temp_multi + iso_multi;
    end
    assign dout = acc_multi;
endmodule
