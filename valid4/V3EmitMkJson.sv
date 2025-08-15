module module_top_level_wrapper (
    input logic        clk_i,
    input logic [7:0]  data_in_i,
    output logic [7:0] result_out_o
);
    localparam int LP_OFFSET = 5;
    parameter int P_WIDTH = 8;
    logic [P_WIDTH-1:0] intermediate_a;
    logic [P_WIDTH-1:0] intermediate_b;
    logic [P_WIDTH-1:0] sum_from_a;
    module_hier_a inst_hier_a (
        .clk_i(clk_i),
        .data_i(data_in_i),
        .sum_o(sum_from_a)
    );
    module_hier_b inst_hier_b (
        .clk_i(clk_i),
        .input_val_i({8'b0, data_in_i}),
        .output_val_o(intermediate_b)
    );
    always_comb begin
        intermediate_a = data_in_i + LP_OFFSET;
        result_out_o = intermediate_a + intermediate_b[7:0] + sum_from_a;
    end
endmodule
interface my_interface;
    logic [15:0] data;
    logic enable;
    modport master (input data, output enable);
    modport slave  (output data, input enable);
endinterface
module (* verilator public *) module_hier_a (
    input logic       clk_i,
    input logic [7:0] data_i,
    output logic [7:0] sum_o
);
    typedef struct packed {
        logic [3:0] field1;
        logic [3:0] field2;
    } my_struct_t;
    typedef enum logic [1:0] {
        STATE_IDLE = 2'b00,
        STATE_RUN  = 2'b01,
        STATE_DONE = 2'b10
    } my_state_e;
    my_struct_t s_var;
    my_state_e current_state;
    logic [7:0] internal_sum_from_class;
    wire [7:0] sub_module_output_val;
    import "DPI-C" function void dpi_dummy_func(input int val);
    class MyDataProcessor;
        rand int m_value;
        int m_offset;
        function new(int offset);
            m_offset = offset;
        endfunction
        function int process(int input_val);
            process = input_val + m_offset;
        endfunction
    endclass
    MyDataProcessor dp_inst;
    always_ff @(posedge clk_i) begin
        if (data_i == 0) begin
            MyDataProcessor temp_dp_inst;
            temp_dp_inst = new(10);
            dp_inst <= temp_dp_inst;
        end else if (dp_inst != null) begin
            internal_sum_from_class <= dp_inst.process(data_i);
            dpi_dummy_func(internal_sum_from_class);
        end
        current_state <= (data_i > 10) ? STATE_RUN : STATE_IDLE;
        s_var.field1 <= data_i[3:0];
        s_var.field2 <= data_i[7:4];
    end
    task automatic calculate_sum(input logic [7:0] a, b, output logic [7:0] sum);
        sum = a + b;
    endtask
    function automatic logic [7:0] get_double(input logic [7:0] val);
        return val * 2;
    endfunction
    always_comb begin
        logic [7:0] temp_sum;
        calculate_sum(internal_sum_from_class, sub_module_output_val, temp_sum);
        sum_o = temp_sum;
    end
    module_hier_a_sub inst_a_sub (
        .clk_i(clk_i),
        .input_val_i(data_i),
        .output_val_o(sub_module_output_val)
    );
endmodule
module (* verilator slow *) module_hier_a_sub (
    input logic        clk_i,
    input logic [7:0]  input_val_i,
    output logic [7:0] output_val_o
);
    logic [7:0] latched_value;
    logic [7:0] dummy_monitor_out;
    always_latch begin
        if (input_val_i > 10) begin
            latched_value = input_val_i;
        end
    end
    always @(posedge clk_i) begin
        assert (latched_value > 10 || input_val_i <= 10);
    end
    assign output_val_o = latched_value;
    bind module_hier_a_sub BoundMonitor bound_monitor_inst (
        .input_val_i_ref(input_val_i),
        .monitor_output_o(dummy_monitor_out)
    );
endmodule
module module_hier_b (
    input logic        clk_i,
    input logic [15:0] input_val_i,
    output logic [15:0] output_val_o
);
    my_interface my_if();
    assign my_if.enable = clk_i;
    always_ff @(posedge clk_i) begin
        fork
            begin : dummy_proc1
                if (input_val_i[0]) begin
                    my_if.data <= input_val_i + 1;
                end else begin
                    my_if.data <= input_val_i;
                end
            end
            begin : dummy_proc2
                if (input_val_i[1]) my_if.enable <= ~my_if.enable;
            end
        join_none
    end
    typedef union packed {
        logic [15:0] word;
        struct packed {
            logic [7:0] byte_h;
            logic [7:0] byte_l;
        } bytes;
    } my_union_t;
    my_union_t u_var;
    logic [15:0] val_from_gen_0;
    logic [15:0] val_from_gen_1;
    genvar i;
    generate
        for (i = 0; i < 2; i++) begin : gen_block
            always_comb begin
                if (i == 0) begin
                    val_from_gen_0 = input_val_i + i;
                end else begin
                    val_from_gen_1 = input_val_i + i;
                end
            end
        end
    endgenerate
    always_comb begin
        logic [15:0] temp_output;
        u_var.word = input_val_i;
        if (u_var.bytes.byte_l == 8'hFF) begin
            u_var.bytes.byte_h = 8'hAA;
            temp_output = u_var.word;
        end else begin
            temp_output = u_var.word;
        end
        temp_output = temp_output + my_if.data;
        temp_output = temp_output + val_from_gen_0 + val_from_gen_1;
        output_val_o = temp_output;
    end
endmodule
module BoundMonitor (
    input logic [7:0] input_val_i_ref,
    output logic [7:0] monitor_output_o
);
    logic [7:0] internal_bound_val;
    always_comb begin
        internal_bound_val = input_val_i_ref + 2;
        if (internal_bound_val > 100) begin
            monitor_output_o = internal_bound_val - 100;
        end else begin
            monitor_output_o = internal_bound_val;
        end
    end
endmodule
