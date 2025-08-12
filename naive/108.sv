module BasicCombinationalLogic (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic       sel,
    output logic [8:0] out_sum,
    output logic [7:0] out_mux,
    output logic       out_eq
);
    parameter P_WIDTH = 8;
    logic [P_WIDTH-1:0] intermediate_and;
    logic [P_WIDTH-1:0] intermediate_or;
    assign intermediate_and = in_a & in_b;
    assign intermediate_or = in_a | in_b;
    always_comb begin
        out_sum = in_a + in_b;
        if (sel) begin
            out_mux = intermediate_and;
        end else begin
            out_mux = intermediate_or;
        end
        out_eq = (in_a == in_b);
    end
endmodule
module SequentialLogicAndTypedefs (
    input logic         clk,
    input logic         reset,
    input logic [15:0]  d_in,
    input logic         enable,
    output logic [15:0] q_out,
    output logic [1:0]  status_code,
    output logic [7:0]  packed_out,
    output logic [15:0] unpacked_out_sum
);
    typedef enum logic [1:0] {
        ST_IDLE = 2'b00,
        ST_BUSY = 2'b01,
        ST_DONE = 2'b10,
        ST_ERROR = 2'b11
    } status_e;
    typedef struct packed {
        logic [3:0] field1;
        logic [3:0] field2;
    } my_packed_s;
    status_e current_status;
    my_packed_s packed_data;
    logic [7:0] unpacked_array [0:1];
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            q_out <= 16'h0000;
            current_status <= ST_IDLE;
            packed_data <= '0;
            unpacked_array[0] <= '0;
            unpacked_array[1] <= '0;
        end else if (enable) begin
            q_out <= d_in;
            current_status <= ST_BUSY;
            packed_data.field1 <= d_in[3:0];
            packed_data.field2 <= d_in[7:4];
            unpacked_array[0] <= d_in[15:8];
            unpacked_array[1] <= d_in[7:0];
        end else begin
            current_status <= ST_DONE;
        end
    end
    assign status_code = current_status;
    assign packed_out = packed_data;
    assign unpacked_out_sum = unpacked_array[0] + unpacked_array[1];
endmodule
class MyConfig;
    rand int config_data;
    function new(int initial_data);
        this.config_data = initial_data;
    endfunction
    function int get_config();
        return config_data;
    endfunction
    function void set_config(int new_data);
        this.config_data = new_data;
    endfunction
endclass
module ClassesAndDynamicStructures (
    input logic         clk,
    input logic         reset,
    input int           cfg_value,
    input logic         data_valid,
    output int          cfg_readback,
    output int unsigned queue_size,
    output int          array_sum
);
    MyConfig my_cfg_obj;
    int dynamic_array[];
    int my_queue[$];
    always_ff @(posedge clk or posedge reset) begin
        int temp_sum; 
        if (reset) begin
            my_cfg_obj = null;
            dynamic_array = new[0];
            my_queue = {};
            cfg_readback <= 0;
            queue_size <= 0;
            array_sum <= 0;
            temp_sum = 0; 
        end else begin
            if (my_cfg_obj == null) begin
                my_cfg_obj = new(100);
            end
            if (data_valid) begin
                my_cfg_obj.set_config(cfg_value);
                dynamic_array = new[2];
                dynamic_array[0] = cfg_value + 1;
                dynamic_array[1] = cfg_value + 2;
                my_queue.push_back(cfg_value + 10);
                my_queue.push_front(cfg_value + 20);
                if (my_queue.size() > 5) begin
                    my_queue.pop_front();
                end
            end
            cfg_readback <= my_cfg_obj.get_config();
            queue_size <= my_queue.size();
            temp_sum = 0; 
            for (int i = 0; i < dynamic_array.size(); i++) begin
                temp_sum += dynamic_array[i];
            end
            array_sum <= temp_sum;
        end
    end
endmodule
module FunctionsAndGenerateBlocks (
    input logic [3:0] data_in_a,
    input logic [3:0] data_in_b,
    input logic       select_func,
    input logic       is_enabled,
    output logic [4:0] result_a,
    output logic [4:0] result_b
);
    localparam L_OFFSET = 1;
    localparam NUM_BLOCKS = 2;
    function automatic logic [4:0] add_one(input logic [3:0] val);
        return val + L_OFFSET;
    endfunction
    task automatic process_data(input logic [3:0] val_a, input logic [3:0] val_b, output logic [4:0] out_val);
        if (val_a > val_b) begin
            out_val = add_one(val_a);
        end else begin
            out_val = add_one(val_b);
        end
    endtask
    logic [4:0] interim_result;
    always_comb begin
        if (is_enabled) begin
            if (select_func) begin
                interim_result = add_one(data_in_a);
            end else begin
                process_data(data_in_a, data_in_b, interim_result);
            end
        end else begin
            interim_result = '0;
        end
    end
    generate
        if (L_OFFSET == 1) begin : gen_offset_1
            assign result_a = interim_result + 1;
        end else begin : gen_offset_other
            assign result_a = interim_result + 2;
        end
    endgenerate
    logic [4:0] gen_loop_results [NUM_BLOCKS-1:0];
    genvar j;
    generate
        for (j = 0; j < NUM_BLOCKS; j++) begin : gen_loop_assigns
            assign gen_loop_results[j] = interim_result + j;
        end
    endgenerate
    assign result_b = gen_loop_results[0] + gen_loop_results[1];
endmodule
module AdvancedDataTypesAndCasting (
    input logic         clk,
    input logic         reset,
    input logic [7:0] in_unsigned,
    input int           in_signed,  
    input logic       union_sel,
    output logic [7:0] assoc_data_out,
    output int         union_val_out,
    output int          cast_result 
);
    typedef union packed {
        int i_val;
        logic [31:0] l_val;
    } my_union_u;
    my_union_u current_union;
    logic [7:0] my_assoc_array [string];
    string key1 = "data_key_1";
    string key2 = "data_key_2";
    logic [7:0] assoc_read_val;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            my_assoc_array.delete();
            current_union = '0; 
        end else begin
            my_assoc_array[key1] = in_unsigned;
            my_assoc_array[key2] = 8'hAA;
            if (union_sel) begin
                current_union.i_val = in_signed;
            end else begin
                current_union.l_val = {24'h0, in_unsigned};
            end
        end
    end
    always_comb begin
        if (my_assoc_array.exists(key1)) begin
            assoc_read_val = my_assoc_array[key1];
        end else begin
            assoc_read_val = 8'hFF;
        end
        if (union_sel) begin
            union_val_out = current_union.i_val;
        end else begin
            union_val_out = int'(current_union.l_val); 
        end
        cast_result = signed'(in_unsigned) + in_signed;
    end
    assign assoc_data_out = assoc_read_val;
endmodule
