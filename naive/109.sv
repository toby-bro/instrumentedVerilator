module CombinationalArithmetic(
    input logic [7:0] a_in,
    input logic [7:0] b_in,
    output logic [8:0] sum_out,
    output logic [7:0] diff_out,
    output logic [7:0] and_out
);
    assign sum_out = a_in + b_in;
    assign diff_out = a_in - b_in;
    assign and_out = a_in & b_in;
endmodule
module SequentialRegister(
    input logic clk,
    input logic rst_n,
    input logic [15:0] d_in,
    input logic shift_en,
    output logic [15:0] q_out,
    output logic [15:0] shifted_q_out
);
    logic [15:0] current_q;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_q <= 16'b0;
        end else begin
            current_q <= d_in;
        end
    end
    logic [15:0] internal_shifted_reg;
    always_ff @(posedge clk) begin
        if (shift_en) begin
            internal_shifted_reg <= current_q << 1; 
        end else begin
            internal_shifted_reg <= current_q;
        end
    end
    assign q_out = current_q;
    assign shifted_q_out = internal_shifted_reg;
endmodule
module StateMachineLogic(
    input logic [1:0] current_state_in,
    input logic enable_in,
    output logic [1:0] next_state_out,
    output logic data_valid_out
);
    typedef enum logic [1:0] {
        IDLE,
        ACTIVE,
        DONE,
        ERROR
    } state_e;
    state_e current_fsm_state;
    always_comb begin
        next_state_out = current_state_in; 
        data_valid_out = 1'b0;
        current_fsm_state = state_e'(current_state_in); 
        case (current_fsm_state)
            IDLE: begin
                if (enable_in) begin
                    next_state_out = ACTIVE;
                end
            end
            ACTIVE: begin
                data_valid_out = 1'b1;
                if (!enable_in) begin
                    next_state_out = DONE;
                end else begin
                    next_state_out = ERROR; 
                end
            end
            DONE: begin
                next_state_out = IDLE;
            end
            ERROR: begin
                next_state_out = ERROR;
            end
            default: begin
                next_state_out = IDLE; 
            end
        endcase
    end
endmodule
module ParameterizedMux #(
    parameter DATA_WIDTH = 8,
    parameter HAS_BYPASS = 1 
) (
    input logic [DATA_WIDTH-1:0] data_in_a,
    input logic [DATA_WIDTH-1:0] data_in_b,
    input logic sel,
    input logic bypass_en, 
    input logic [DATA_WIDTH-1:0] bypass_data, 
    output logic [DATA_WIDTH-1:0] data_out
);
    logic [DATA_WIDTH-1:0] mux_result;
    always_comb begin
        if (sel) begin
            mux_result = data_in_b;
        end else begin
            mux_result = data_in_a;
        end
    end
    generate
        if (HAS_BYPASS == 1) begin : bypass_logic
            always_comb begin
                if (bypass_en) begin
                    data_out = bypass_data;
                end else begin
                    data_out = mux_result;
                end
            end
        end else begin : no_bypass_logic
            assign data_out = mux_result;
        end
    endgenerate
endmodule
module ComplexDataProcessor (
    input logic [3:0] input_array_a [2], 
    input logic [3:0] input_array_b [2],
    input logic         process_cmd,
    output logic [7:0]  result_sum,
    output logic [3:0]  max_val_in_a
);
    typedef struct packed {
        logic [7:0] value;
        logic valid;
    } s_data_t;
    task automatic calculate_sum(
        input logic [3:0] arr_a [2],
        input logic [3:0] arr_b [2],
        output logic [7:0] sum
    );
        sum = 8'b0;
        for (int i = 0; i < 2; i++) begin
            sum += arr_a[i] + arr_b[i];
        end
    endtask
    function automatic logic [3:0] find_max(
        input logic [3:0] arr [2]
    );
        logic [3:0] current_max = 4'b0;
        for (int i = 0; i < 2; i++) begin
            if (arr[i] > current_max) begin
                current_max = arr[i];
            end
        end
        return current_max;
    endfunction
    s_data_t internal_data_a; 
    always_comb begin
        internal_data_a.value = 8'hAA; 
        internal_data_a.valid = 1'b1;
        result_sum = 8'b0;
        max_val_in_a = 4'b0;
        if (process_cmd) begin
            calculate_sum(input_array_a, input_array_b, result_sum);
            max_val_in_a = find_max(input_array_a);
        end else begin
            result_sum = internal_data_a.value; 
            max_val_in_a = 4'b0;
        end
    end
endmodule
module ClassUserModule (
    input logic [7:0] input_val,
    input logic       update_en,
    output logic [7:0] output_val
);
    class MySimpleClass;
        logic [7:0] internal_data;
        function new();
            internal_data = 8'b0;
        endfunction
        function void set_data(logic [7:0] val);
            internal_data = val;
        endfunction
        function logic [7:0] get_data();
            return internal_data;
        endfunction
    endclass : MySimpleClass
    MySimpleClass my_instance; 
    always_comb begin
        if (my_instance == null) begin
            my_instance = new();
        end
        if (update_en) begin
            my_instance.set_data(input_val);
        end
        output_val = my_instance.get_data();
    end
endmodule
module LatchAndPriorityMux (
    input logic [7:0] in_data,
    input logic [1:0] select_code,
    output logic [7:0] out_data_mux,
    output logic [7:0] latched_data 
);
    logic [7:0] internal_mux_out;
    always_comb begin
        internal_mux_out = 8'b0; 
        case (select_code)
            2'b00: internal_mux_out = in_data;
            2'b01: internal_mux_out = in_data + 8'd1;
            2'b10: internal_mux_out = in_data - 8'd1;
            default: internal_mux_out = 8'hFF; 
        endcase
    end
    always_latch begin
        if (select_code == 2'b11) begin 
            latched_data = in_data;
        end
    end
    assign out_data_mux = internal_mux_out;
endmodule
module SimpleCounter (
    input logic clk,
    input logic reset_n,
    input logic count_en,
    output logic [7:0] count_out,
    output logic       max_count_reached
);
    logic [7:0] counter_reg;
    localparam MAX_COUNT = 8'd250;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            counter_reg <= 8'b0;
        end else if (count_en) begin
            if (counter_reg == MAX_COUNT) begin
                counter_reg <= 8'b0; 
            end else begin
                counter_reg <= counter_reg + 1;
            end
        end
    end
    assign count_out = counter_reg;
    assign max_count_reached = (counter_reg == MAX_COUNT) && count_en;
endmodule
module NestedStructAndArray (
    input logic [3:0] array_of_values[4], 
    input logic       enable_processing,
    output logic      any_value_above_threshold,
    output logic [7:0] total_sum_of_processed
);
    typedef struct packed {
        logic [3:0] val1;
        logic [3:0] val2;
    } two_vals_t;
    typedef struct {
        two_vals_t pairs[2]; 
        logic [7:0] extra_info;
    } complex_data_t;
    complex_data_t my_complex_data;
    logic [7:0] internal_sum;
    logic       internal_flag;
    localparam THRESHOLD = 4'd10;
    always_comb begin
        internal_sum = 8'b0;
        internal_flag = 1'b0;
        my_complex_data.pairs[0].val1 = array_of_values[0];
        my_complex_data.pairs[0].val2 = array_of_values[1];
        my_complex_data.pairs[1].val1 = array_of_values[2];
        my_complex_data.pairs[1].val2 = array_of_values[3];
        my_complex_data.extra_info = 8'hAB; 
        if (enable_processing) begin
            for (int i = 0; i < 2; i++) begin
                if (my_complex_data.pairs[i].val1 > THRESHOLD || my_complex_data.pairs[i].val2 > THRESHOLD) begin
                    internal_flag = 1'b1;
                end
                internal_sum += my_complex_data.pairs[i].val1 + my_complex_data.pairs[i].val2;
            end
            internal_sum += my_complex_data.extra_info;
        end else begin
            internal_sum = 8'b0; 
            internal_flag = 1'b0;
        end
        any_value_above_threshold = internal_flag;
        total_sum_of_processed = internal_sum;
    end
endmodule
