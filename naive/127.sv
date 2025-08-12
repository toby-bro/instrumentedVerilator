module SimpleCombinational (
    input logic in_a,
    input logic in_b,
    output logic out_xor,
    output logic out_and
);
    parameter WIDTH = 2;
    localparam CONST_VAL = 3'b101;
    logic internal_wire;
    assign internal_wire = in_a & in_b;
    always_comb begin
        out_xor = in_a ^ in_b;
        out_and = internal_wire;
    end
endmodule
module SequentialEnumState (
    input logic clk,
    input logic rst_n,
    input logic [7:0] data_in,
    input logic enable,
    output logic [7:0] data_out,
    output logic [1:0] state_current
);
    typedef enum logic [1:0] {
        STATE_IDLE,
        STATE_LOAD,
        STATE_PROCESS,
        STATE_DONE
    } fsm_state_e;
    fsm_state_e current_state_q, next_state_n;
    logic [7:0] data_reg_q;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state_q <= STATE_IDLE;
            data_reg_q <= 8'b0;
        end else begin
            current_state_q <= next_state_n;
            if (current_state_q == STATE_LOAD) begin
                data_reg_q <= data_in;
            end
        end
    end
    always_comb begin
        next_state_n = current_state_q;
        data_out = data_reg_q;
        state_current = current_state_q;
        case (current_state_q)
            STATE_IDLE: begin
                if (enable) begin
                    next_state_n = STATE_LOAD;
                end
            end
            STATE_LOAD: begin
                next_state_n = STATE_PROCESS;
            end
            STATE_PROCESS: begin
                if (data_reg_q > 8'd100) begin
                    next_state_n = STATE_DONE;
                end else begin
                    next_state_n = STATE_IDLE;
                end
            end
            STATE_DONE: begin
                next_state_n = STATE_IDLE;
            end
            default: begin
                next_state_n = STATE_IDLE;
            end
        endcase
    end
endmodule
module StructAndArrayProc (
    input logic [1:0] ctrl_i,
    input logic [7:0] data_in_array [0:3],
    output logic [7:0] data_out_sum,
    output logic [1:0] status_o
);
    typedef struct packed {
        logic       valid;
        logic [6:0] value;
    } my_data_s;
    my_data_s processed_data;
    logic [7:0] temp_sum;
    logic [1:0] current_status;
    always_comb begin
        temp_sum = 8'b0;
        current_status = 2'b00;
        processed_data.valid = 1'b0;
        processed_data.value = 7'b0;
        for (int i = 0; i < 4; i++) begin
            if (ctrl_i == 2'b01) begin
                temp_sum = temp_sum + data_in_array[i];
                current_status = 2'b01;
            end else if (ctrl_i == 2'b10 && i < 2) begin
                temp_sum = temp_sum + data_in_array[i];
                current_status = 2'b10;
            end
        end
        if (temp_sum > 8'd100) begin
            processed_data.valid = 1'b1;
            processed_data.value = temp_sum[6:0];
            current_status = 2'b11;
        end
        data_out_sum = temp_sum;
        status_o = current_status;
    end
endmodule
class SimpleDataContainer;
    logic [7:0] data_value;
    logic       is_valid;
    int         transaction_count;
    function new(logic [7:0] initial_data);
        data_value = initial_data;
        is_valid = 1'b0;
        transaction_count = 0;
    endfunction
    function void update_data(logic [7:0] new_data);
        data_value = new_data;
        is_valid = 1'b1;
        transaction_count++;
    endfunction
    function logic [7:0] get_data();
        return data_value;
    endfunction
    function bit get_valid();
        return is_valid;
    endfunction
endclass
module ClassInstanceModule (
    input logic [7:0] input_val,
    input logic       input_enable,
    output logic [7:0] output_val,
    output logic       output_valid
);
    SimpleDataContainer my_container;
    always_ff @(posedge input_enable) begin
        if (my_container == null) begin
            my_container = new(input_val);
        end else begin
            my_container.update_data(input_val);
        end
    end
    always_comb begin
        if (my_container == null) begin
            output_val = 8'b0;
            output_valid = 1'b0;
        end else begin
            output_val = my_container.get_data();
            output_valid = my_container.get_valid();
        end
    end
endmodule
module FunctionsAndTasksModule (
    input logic [7:0] in_data_a,
    input logic [7:0] in_data_b,
    input logic       in_select,
    output logic [7:0] out_result,
    output logic       out_status
);
    function automatic logic [7:0] calculate_sum(logic [7:0] val1, logic [7:0] val2);
        return val1 + val2;
    endfunction
    task automatic check_status(input logic [7:0] current_sum, output logic status_flag);
        if (current_sum > 8'd200) begin
            status_flag = 1'b1;
        end else begin
            status_flag = 1'b0;
        end
    endtask
    logic [7:0] temp_sum;
    logic proc_status;
    always_comb begin
        if (in_select) begin
            temp_sum = calculate_sum(in_data_a, in_data_b);
        end else begin
            temp_sum = in_data_a - in_data_b;
        end
        check_status(temp_sum, proc_status);
        out_result = temp_sum;
        out_status = proc_status;
    end
endmodule
module GenerateBlockExample (
    input logic [7:0] data_in_gen,
    input logic [3:0] control_en_gen,
    output logic [7:0] data_out_gen
);
    localparam NUM_BLOCKS = 4;
    logic [7:0] intermediate_data [NUM_BLOCKS-1:0];
    generate
        genvar i;
        for (i = 0; i < NUM_BLOCKS; i = i + 1) begin : gen_data_proc
            if (i == 0) begin : first_processor
                always_comb begin
                    if (control_en_gen[i]) begin
                        intermediate_data[i] = data_in_gen + 8'd1;
                    end else begin
                        intermediate_data[i] = data_in_gen;
                    end
                end
            end else if (i == 1) begin : second_processor
                always_comb begin
                    if (control_en_gen[i]) begin
                        intermediate_data[i] = data_in_gen * 8'd2;
                    end else begin
                        intermediate_data[i] = data_in_gen;
                    end
                end
            end else begin : generic_processor
                always_comb begin
                    if (control_en_gen[i]) begin
                        intermediate_data[i] = data_in_gen | {8{1'b1}};
                    end else begin
                        intermediate_data[i] = data_in_gen & {8{1'b0}};
                    end
                end
            end
        end
    endgenerate
    always_comb begin
        data_out_gen = 8'b0;
        for(int k=0; k < NUM_BLOCKS; k++) begin
            if (control_en_gen[k]) begin
                 data_out_gen = data_out_gen + intermediate_data[k];
            end
        end
    end
endmodule
module AssociativeArrayAndTypedef (
    input byte key_in,
    input int val_in,
    input logic write_en,
    input logic read_en,
    output int read_val_out,
    output logic is_key_found
);
    typedef int assoc_map_t[byte];
    assoc_map_t my_map;
    logic current_key_found;
    int current_read_val;
    always_comb begin
        current_read_val = 0;
        current_key_found = 1'b0;
        if (write_en) begin
            my_map[key_in] = val_in;
        end
        if (read_en) begin
            if (my_map.exists(key_in)) begin
                current_read_val = my_map[key_in];
                current_key_found = 1'b1;
            end else begin
                current_key_found = 1'b0;
                current_read_val = -1;
            end
        end else begin
            current_key_found = 1'b0;
            current_read_val = 0;
        end
        read_val_out = current_read_val;
        is_key_found = current_key_found;
    end
endmodule
