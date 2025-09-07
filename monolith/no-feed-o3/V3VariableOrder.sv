module variable_order_basic(
    input  logic        clk,
    input  logic [31:0] din,
    output logic [31:0] dout
);
    static logic [3:0]  s_static_var;       
    logic               single_bit;         
    logic [7:0]         byte_var;           
    logic [15:0]        half_var;           
    logic [31:0]        word_var;           
    logic [63:0]        dword_var;          
    logic [127:0]       big_var;            
    logic [7:0]         unpack_arr [0:3];   
    always_ff @(posedge clk) begin
        single_bit      <= din[0];
        byte_var        <= din[7:0];
        half_var        <= din[15:0];
        word_var        <= din;
        dword_var       <= {din, din};
        big_var         <= {din, din, din, din};
        unpack_arr[0]   <= din[7:0];
        unpack_arr[1]   <= din[15:8];
        unpack_arr[2]   <= din[23:16];
        unpack_arr[3]   <= din[31:24];
        s_static_var    <= din[3:0];
    end
    assign dout = word_var;
endmodule
module unpack_array_module(
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    logic [7:0] memory [0:15];    
    always_comb begin
        memory[0] = in_data;
        out_data  = memory[0];
    end
endmodule
module used_clock_module(
    input  logic clk,
    input  logic rst_n,
    output logic flag
);
    logic state;
    always_ff @(posedge clk) begin
        if (!rst_n) state <= 1'b0;
        else        state <= ~state;
    end
    assign flag = state;
endmodule
module big_alignment_module(
    input  logic [127:0] bus_in,
    output logic [127:0] bus_out
);
    logic [127:0] reg128;
    always_comb begin
        reg128 = bus_in;
    end
    assign bus_out = reg128;
endmodule
module class_in_proc(
    input  logic sig_in,
    output logic sig_out
);
    class simple_c;
        bit val;
        function new(bit v = 0); val = v; endfunction
    endclass
    always_comb begin
        simple_c c_inst = new(sig_in);
        sig_out = c_inst.val;
    end
endmodule
module gather_mtask_affinity_test(
    input  logic clk,
    input  logic data_in,
    output logic data_out
);
    logic internal_reg;
    always_ff @(posedge clk) begin
        internal_reg <= data_in;
    end
    assign data_out = internal_reg;
endmodule
module var_tsp_sorter_test(
    input  logic [3:0] a,
    output logic [3:0] y
);
    logic [3:0] array32 [0:3];
    always_comb begin
        array32[0] = a;
        array32[1] = ~a;
        array32[2] = a & 4'hF;
        array32[3] = a | 4'h0;
        y = array32[0];
    end
endmodule
module variable_order_process(
    input  logic [15:0] in_a,
    output logic [15:0] out_a
);
    static logic [63:0] s64;          
    logic [31:0]        loc32;        
    logic [15:0]        loc16 [0:1];  
    always_comb begin
        s64      = {48'd0, in_a};
        loc16[0] = in_a;
        loc16[1] = ~in_a;
        loc32    = {16'd0, loc16[0]};
    end
    assign out_a = loc32[15:0];
endmodule
