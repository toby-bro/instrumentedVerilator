module active (
    input wire clk,
    input wire rst_n,
    input wire [7:0] data_in,
    input wire enable,
    input wire select,
    output reg [7:0] data_out,
    output reg [7:0] latch_out,
    output reg [7:0] comb_out,
    output reg valid
);

    // Wire assignment - will be moved to SACTIVE(combo)
    wire [7:0] intermediate = data_in & {8{enable}};
    
    // Initial block - will be moved to IACTIVE
    initial begin
        data_out = 8'h00;
        valid = 1'b0;
        latch_out = 8'h00;
    end
    
    // Final block
    final begin
        $display("Simulation finished with data_out = %h", data_out);
    end
    
    // Sequential always block - will be processed as clocked
    // Uses 'always @(posedge clk or negedge rst_n)' for edge-sensitive sequential logic (flip-flops).
    // This is the traditional Verilog way. SystemVerilog also offers 'always_ff'.
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_out <= 8'h00;
            valid <= 1'b0;
        end else if (enable) begin
            data_out <= data_in;
            valid <= 1'b1;
            // This will trigger BLKSEQ warning
            comb_out = data_in + 8'h01;
        end else begin
            valid <= 1'b0;
        end
    end
    
    // Combinational always block - will be recognized as combo
    // Uses 'always @*' which implicitly senses all signals read inside.
    // Intended for combinational logic. SystemVerilog's 'always_comb' is generally preferred
    // as it adds more checks to ensure purely combinational behavior.
    always @* begin
        comb_out = data_in + 8'h01;
    end
    
    // Latch behavior - will trigger latch detection
    // Uses 'always @(explicit sensitivity list)' for level-sensitive logic.
    // Because 'latch_out' is not assigned in all code paths (implicitly retains its value
    // when 'enable' is false), this infers a latch. Using 'always_latch' makes this intent clearer.
    always @(enable or data_in) begin
        if (enable) begin
            latch_out = data_in;
        // The 'else' path was added to explicitly show how to *avoid* a latch
        // in a standard 'always' block if combinational logic was intended.
        // If the 'else' was missing, a latch would be inferred.
        end else begin
        // Add explicit else path to avoid latch
        latch_out = latch_out; // Or specify a default value like 8'h00
        end
        // No else path creates a latch
    end
    
    // Always latch - expected latch behavior
    // Uses 'always_latch', the preferred SystemVerilog construct for intentionally modeling
    // level-sensitive latches. It implicitly determines the sensitivity list and signals
    // latch intent clearly.
    always_latch begin
        if (select) begin
            // latch_out retains its previous value if 'select' is false, creating latch behavior.
            latch_out = data_in ^ 8'hFF;
        end
    end

endmodule