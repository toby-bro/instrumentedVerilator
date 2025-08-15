typedef enum {
    IDLE,
    ACTIVE,
    DONE
} State_e;
module DataFlowAndParams(
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic       in_en,
    output logic [15:0] out_sum,
    output logic [7:0]  out_diff,
    output logic        out_logic
);
    parameter int PARAM_OFFSET = 10;
    localparam string LOCALPARAM_STR = "Hello Verilog";
    localparam real LOCALPARAM_PI = 3.14159265;
    logic [3:0] s_count;
    typedef struct packed {
        logic [7:0] addr;
        logic [3:0] len;
    } PacketHeader_t;
    PacketHeader_t header_inst;
    typedef union packed {
        logic [15:0] word;
        struct packed {
            logic [7:0] byte_high;
            logic [7:0] byte_low;
        } bytes;
    } WordBytes_t;
    WordBytes_t wb_inst;
    State_e current_state;
    function automatic logic [7:0] calculate_diff(input logic [7:0] val1, input logic [7:0] val2);
        return (val1 > val2) ? (val1 - val2) : (val2 - val1);
    endfunction
    task automatic update_state(input State_e next_state);
        current_state = next_state;
    endtask
    always_comb begin
        out_sum = {in_a, 8'b0} + {in_b, 8'b0} + PARAM_OFFSET;
        out_diff = calculate_diff(in_a, in_b);
        out_logic = in_en && (s_count > 0);
        header_inst.addr = in_a;
        header_inst.len = 4'd4;
        wb_inst.word = out_sum;
        if (wb_inst.bytes.byte_high > 0) begin
            out_logic = ~out_logic;
        end
        if ($bits(in_a) == 8 && $clog2(PARAM_OFFSET) == 4) begin
            s_count = 4'hF;
        end else begin
            s_count = 4'h0;
        end
        if (in_en) update_state(ACTIVE);
        else update_state(IDLE);
    end
endmodule
module ClassAndCoverage(
    input logic clk,
    input logic rst_n,
    input logic [3:0] data_in,
    input logic enable_cov,
    output logic [3:0] data_out
);
    import "DPI-C" function int dpi_multiply(input int a, input int int_b);
    class MyProcessor;
        logic [3:0] internal_data;
        int         processed_count;
        string      name_str;
        function new();
            internal_data = 4'h0;
            processed_count = 0;
            name_str = "ProcessorInst";
        endfunction
        function automatic logic [3:0] process(input logic [3:0] in_val);
            internal_data = in_val;
            processed_count++;
            return internal_data;
        endfunction
        task automatic reset_processor();
            internal_data = 4'h0;
            processed_count = 0;
        endtask
    endclass
    MyProcessor proc_inst;
    logic [3:0] processed_val;
    int dpi_result;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            if (proc_inst == null) begin
                proc_inst <= new();
            end
            proc_inst.reset_processor();
            processed_val <= 4'h0;
            dpi_result <= 0;
        end else begin
            if (proc_inst == null) begin
                proc_inst <= new();
            end
            processed_val <= proc_inst.process(data_in);
            proc_inst.reset_processor();
            dpi_result <= dpi_multiply(data_in, 2);
        end
    end
    assign data_out = processed_val;
endmodule
module ComplexTypesAndTracing(
    input logic         trace_in_scalar,
    input logic [7:0]   trace_in_packed_array,
    input logic [3:0]   trace_in_unpacked_array [7:0],
    input State_e       trace_in_enum_sel,
    input real          trace_in_real,
    output logic [127:0] trace_out_wide,
    output logic [63:0]  trace_out_quad,
    output event        trace_out_event,
    inout logic [1:0]   inout_port_example
);
    logic one_bit_sig;
    logic [7:0] eight_bit_sig;
    logic [15:0] sixteen_bit_sig;
    logic [31:0] thirty_two_bit_sig;
    logic [63:0] sixty_four_bit_sig;
    logic [127:0] one_twenty_eight_bit_sig;
    real real_internal_var;
    event internal_event;
    logic [1:0] my_unpacked_array [7:0];
    State_e current_internal_state;
    always_comb begin
        one_bit_sig = trace_in_scalar;
        eight_bit_sig = trace_in_packed_array;
        sixteen_bit_sig = {8'h0, eight_bit_sig};
        thirty_two_bit_sig = {16'h0, sixteen_bit_sig};
        sixty_four_bit_sig = {32'h0, thirty_two_bit_sig};
        one_twenty_eight_bit_sig = {64'h0, sixty_four_bit_sig};
        trace_out_wide = one_twenty_eight_bit_sig;
        trace_out_quad = sixty_four_bit_sig;
        for (int i=0; i<8; i++) begin
            my_unpacked_array[i] = trace_in_unpacked_array[i][1:0];
        end
        real_internal_var = trace_in_real * 2.0;
        -> internal_event;
        current_internal_state = trace_in_enum_sel;
        -> trace_out_event;
        inout_port_example = {trace_in_scalar, trace_in_scalar};
    end
endmodule
