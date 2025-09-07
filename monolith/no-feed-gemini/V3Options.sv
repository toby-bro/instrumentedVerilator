`timescale 1ns/1ps
module ModOptionsTimescale (
    input logic [7:0] in_data,
    output logic [7:0] out_result
);
    parameter DEFAULT_VALUE = 8'd10;
    localparam MAX_LIMIT = DEFAULT_VALUE * 2;
    logic [7:0] internal_reg;
    always_comb begin
        if (in_data > MAX_LIMIT) begin
            internal_reg = in_data - MAX_LIMIT;
        end else begin
            internal_reg = in_data + DEFAULT_VALUE;
        end
        out_result = internal_reg;
    end
    class MySimpleClass;
        int m_val;
        function new(int val);
            m_val = val;
        endfunction
        function int get_val();
            return m_val;
        endfunction
    endclass
    function automatic int process_data(int data);
        MySimpleClass obj = new(data); 
        return obj.get_val();
    endfunction
    logic [31:0] temp_processed_val;
    always_comb begin
        temp_processed_val = process_data(in_data);
    end
endmodule
module ModDPIAndTypes (
    input bit [31:0] input_vec,
    output int output_int_val
);
    import "DPI-C" function int c_add_one(int val);
    import "DPI-C" function void c_process_data(string data_str, int data_len);
    export "DPI-C" function sv_get_current_value;
    function int sv_get_current_value();
        return c_add_one(input_vec); 
    endfunction
    typedef enum {RED, GREEN, BLUE} color_e;
    typedef struct packed {
        bit [2:0] field1;
        logic     field2;
        int       field3;
    } my_struct_t;
    typedef union packed {
        int i_val;
        byte b_arr [4];
    } my_union_t;
    color_e current_color;
    my_struct_t current_struct;
    my_union_t current_union;
    always_comb begin
        output_int_val = c_add_one(input_vec); 
        current_color = GREEN;
        current_struct = '{3'b101, 1'b0, 123};
        current_union.i_val = output_int_val;
        c_process_data("hello_world", $bits(input_vec));
    end
    class NestedClass;
        int nested_val;
        function new(int val);
            nested_val = val;
        endfunction
    endclass
    function automatic int get_nested_val_from_obj(int init_val);
        NestedClass nested_obj = new(init_val);
        return nested_obj.nested_val;
    endfunction
    logic [31:0] complex_val;
    always_comb begin
        complex_val = get_nested_val_from_obj(input_vec);
    end
endmodule
`define ENABLE_FEATURE_A
`define DEBUG_MODE 1
module ModDefinesAndIncludes (
    input logic [15:0] control_sig,
    output logic output_flag
);
    logic [15:0] internal_control;
`ifdef ENABLE_FEATURE_A
    `include "path/to/included_file_A.sv" 
    localparam FEATURE_A_ENABLED = 1;
`else
    localparam FEATURE_A_ENABLED = 0;
`endif
`ifndef FEATURE_B
    `include "relative_included_file_B.v" 
`endif
`undef DEBUG_MODE 
`define MAX_COUNT 100
    always_comb begin
        internal_control = control_sig;
        if (FEATURE_A_ENABLED && internal_control < `MAX_COUNT) begin
            output_flag = 1'b1;
        end else begin
            output_flag = 1'b0;
        end
    end
    logic [31:0] complex_calc;
    always_comb begin
        complex_calc = ((control_sig + `MAX_COUNT) * (control_sig - 5)) / (control_sig + 1);
    end
    integer  int_val;
    longint  long_val;
    byte     byte_val;
    always_comb begin
        int_val = control_sig;
        long_val = int_val * 1000;
        byte_val = long_val[7:0];
    end
endmodule
module ModGenerateAndUnroll (
    input logic [3:0] in_count,
    output logic [7:0] out_sum
);
    genvar i;
    logic [7:0] partial_sums [4];
    generate
        for (i = 0; i < 4; i = i + 1) begin : sum_gen
            always_comb begin
                partial_sums[i] = in_count + i;
            end
        end
    endgenerate
    logic [7:0] current_sum = 0;
    always_comb begin
        for (i = 0; i < 4; i = i + 1) /* verilator unroll_full */ begin
            current_sum = current_sum + partial_sums[i];
        end
        out_sum = current_sum;
    end
    logic [7:0] ff_reg;
    input logic clk_in;
    input logic latch_en;
    always_ff @(posedge clk_in) begin
        ff_reg <= in_count + out_sum;
    end
    logic [7:0] latch_reg;
    always_latch begin
        if (latch_en) begin
            latch_reg = ff_reg;
        end
    end
    class EmptyClass;
    endclass
    function automatic void create_empty_obj();
        EmptyClass empty_obj = new();
    endfunction
    always_comb begin
        create_empty_obj();
    end
endmodule
module ModComplexFeatures (
    input logic [31:0] input_val_a,
    input logic [31:0] input_val_b,
    output logic [31:0] output_val
);
    logic [31:0] unused_signal; 
    parameter UNUSED_PARAM = 5; 
    typedef enum logic [1:0] {
        STATE_IDLE = 2'b00,
        STATE_RUN  = 2'b01,
        STATE_DONE = 2'b10
    } state_t;
    state_t current_state;
    logic [7:0] narrow_result;
    always_comb begin
        narrow_result = input_val_a + input_val_b; 
        current_state = STATE_RUN; 
    end
    logic [31:0] temp_val;
    logic [15:0] half_val;
    always_comb begin
        temp_val = (input_val_a > input_val_b) ? (input_val_a | input_val_b) : (input_val_a & input_val_b);
        half_val = temp_val[15:0];
        output_val = {narrow_result, half_val[15:8], temp_val[7:0]}; 
    end
    wire [31:0] assign_wire;
    assign assign_wire = input_val_a ^ input_val_b;
    function automatic bit check_condition(int val);
        return (val > 100);
    endfunction
    always_comb begin
        assert (check_condition(input_val_a)) else $error("Input A is too small!");
    end
    always_comb begin
        for (int k = 0; k < 1; k++) begin 
        end
    end
endmodule
module ModComplexClass (
    input int start_count,
    output int final_count
);
    class DataContainer;
        int data_array[];
        function new(int size);
            data_array = new[size];
            foreach (data_array[idx]) begin
                data_array[idx] = idx;
            end
        endfunction
        function void modify_data(int multiplier);
            for (int idx = 0; idx < data_array.size(); idx++) begin
                data_array[idx] *= multiplier;
            end
        endfunction
        function int sum_data();
            int sum = 0;
            for (int idx = 0; idx < data_array.size(); idx++) begin
                sum += data_array[idx];
            end
            return sum;
        endfunction
    endclass
    DataContainer container_obj;
    function automatic int setup_and_calculate(int init_size, int mult);
        container_obj = new(init_size); 
        container_obj.modify_data(mult);
        return container_obj.sum_data();
    endfunction
    always_comb begin
        final_count = setup_and_calculate(start_count < 1 ? 1 : start_count, 2);
    end
endmodule
