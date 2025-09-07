module shadow_scalar_mod (
    input  logic        clk,
    input  logic [7:0]  din,
    output logic [7:0]  q
);
    always_ff @(posedge clk) begin
        q <= din;               
    end
endmodule
module shadow_masked_mod (
    input  logic        clk,
    input  logic [7:0]  din_a,
    input  logic [7:0]  din_b,
    output logic [7:0]  data
);
    always_comb begin
        data[3:0] = din_a[3:0];
    end
    always_ff @(posedge clk) begin
        data[7:4] <= din_b[7:4];
    end
endmodule
module flag_shared_mod (
    input  logic        clk,
    input  logic [1:0]  idx,
    input  logic [7:0]  din,
    output logic [7:0]  dout
);
    logic [7:0] mem [0:3];      
    always_ff @(posedge clk) begin
        mem[idx] <= din;        
    end
    assign dout = mem[idx];
endmodule
module flag_unique_mod (
    input  logic        clk,
    input  logic [7:0]  din1,
    input  logic [7:0]  din2,
    output logic [7:0]  q
);
    always_ff @(posedge clk) fork
        q <= din1;              
        q <= din2;              
    join
endmodule
module val_queue_whole_mod (
    input  logic        clk,
    input  logic [7:0]  din,
    input  logic [3:0]  rd_idx,
    output logic [7:0]  dout
);
    logic [7:0] arr [0:15];     
    always_ff @(posedge clk) begin
        integer i;
        i = 0;
        while (i < 16) begin
            arr[i] <= din;      
            i = i + 1;
        end
    end
    assign dout = arr[rd_idx];
endmodule
module val_queue_partial_mod (
    input  logic        clk,
    input  logic [7:0]  din,
    input  logic [3:0]  wr_idx,
    input  logic [3:0]  rd_idx,
    output logic [7:0]  dout
);
    logic [7:0] mem [0:15];
    always_ff @(posedge clk) begin
        integer k;
        k = 0;
        while (k < 4) begin
            mem[wr_idx + k][3:0] <= din[3:0]; 
            k = k + 1;
        end
    end
    assign dout = mem[rd_idx];
endmodule
module event_trigger_mod (
    input  logic clk,
    output logic event_seen
);
    event ev;
    always_ff @(posedge clk) begin
        ->> ev;                 
    end
    always @(ev) begin
        event_seen <= 1'b1;     
    end
endmodule
