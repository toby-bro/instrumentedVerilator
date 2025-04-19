module splitVar (
    input  logic clk,
    input  logic rst_n,
    input  logic [3:0] in_port, // Removed split_var since ports are public by default
    output logic [3:0] out_port // Removed split_var since ports are public by default
);
    // Unpacked arrays with split_var attribute
    /* verilator lint_off ALWCOMBORDER */
    logic [1:0] unpacked_array_var[0:1] /*verilator split_var*/;
    /* verilator lint_on ALWCOMBORDER */
    
    // Packed variables with split_var attribute
    logic [7:0] packed_var /*verilator split_var*/;
    logic [3:0][1:0] packed_array /*verilator split_var*/;
    
    // Variables that shouldn't be split (for warning/error cases)
    logic single_bit; // Can't split 1-bit variables
    logic [3:0] no_attribute; // No split_var attribute
    logic [1:0] unpacked_inout[0:1]; // Will be used for inout (can't split)
    
    // This won't be split but we'll use lint_off to silence the warning
    /* verilator lint_off SPLITVAR */
    logic [7:0] public_var /*verilator public*//*verilator split_var*/;
    /* verilator lint_on SPLITVAR */
    
    // Reference to unpacked array in always blocks
    always_comb begin
        unpacked_array_var[1][0] = unpacked_array_var[0][0]; // UNOPTFLAT warning silenced with lint_off
        unpacked_array_var[1][1] = ~unpacked_array_var[0][1]; // UNOPTFLAT warning silenced with lint_off
    end
    
    // Reference to packed variable with different access patterns
    always_comb begin
        if (in_port[0]) begin
            packed_var = 8'b0; // Full assignment
        end else begin
            packed_var[7] = in_port[3];   // Bit select
            packed_var[6:4] = in_port[2:0]; // Part select
            packed_var[3:0] = unpacked_array_var[0]; // Mixing unpacked and packed
        end
    end
    
    // Reference in sensitivity list
    always @(packed_var[3:0], unpacked_array_var[0]) begin
        no_attribute = packed_var[3:0];
    end
    
    // Non-blocking assignments
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            packed_array <= '0;
        end else begin
            packed_array[0] <= unpacked_array_var[0];
            packed_array[1] <= unpacked_array_var[1];
            packed_array[3:2] <= {unpacked_array_var[1], unpacked_array_var[0]};
        end
    end
    
    // Complex expressions with packed variables
    always_comb begin
        out_port = packed_var[7:4] & packed_var[3:0];
    end
    
    // Task with split variables
    task automatic process_data;
        input logic [7:0] data /*verilator split_var*/;
        begin
            packed_var = data;
            unpacked_array_var[0][0] = data[0];
            unpacked_array_var[0][1] = data[1];
            unpacked_array_var[1][0] = data[2];
            unpacked_array_var[1][1] = data[3];
        end
    endtask
    
    // Function with split variables
    function automatic logic [3:0] compute;
        input logic [3:0] in_data /*verilator split_var*/;
        logic [3:0] result /*verilator split_var*/;
        begin
            result = in_data ^ packed_var[3:0];
            compute = result;
        end
    endfunction
    
    // Initial block 
    initial begin
        packed_var = 8'h55;
        unpacked_array_var[0] = 2'b10;
        unpacked_array_var[1] = 2'b01;
        
        // Call the task
        process_data(8'hAA);
        
        // Call the function
        no_attribute = compute(4'h5);
    end
    
    // Testing variable access through instantiated modules
    sub_module sub_inst (
        .clk(clk),
        .data_in(packed_var),
        .data_out(no_attribute)
    );
    
    // Another module that has a port with split_var
    split_port_module split_port_inst (
        .in_value(packed_var)
    );
    
endmodule

// Submodule for port connections
module sub_module (
    input logic clk,
    input logic [7:0] data_in,
    output logic [3:0] data_out
);
    always_ff @(posedge clk) begin
        data_out <= data_in[3:0];
    end
endmodule

// Module with split_var port - will use a local private variable that can be split
module split_port_module (
    input logic [7:0] in_value
);
    logic [7:0] internal_copy /*verilator split_var*/;
    
    always_comb begin
        internal_copy[7:4] = in_value[3:0];
        internal_copy[3:0] = in_value[7:4];
    end
endmodule
