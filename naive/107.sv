module SimpleCombinationalLogic (
    input  logic [7:0] a_in,
    input  logic [7:0] b_in,
    output logic [8:0] sum_out,
    output logic       a_is_greater
);
    logic [7:0] temp_b_inverted;
    logic       equality_flag;
    assign sum_out = a_in + b_in;
    assign a_is_greater = (a_in > b_in) ? 1'b1 : 1'b0;
    always_comb begin
        temp_b_inverted = ~b_in;
        equality_flag = (a_in == temp_b_inverted);
    end
endmodule
module BasicSequentialLogic (
    input  logic clk,
    input  logic rst_n,
    input  logic enable_count,
    output logic [3:0] counter_val_out
);
    logic [3:0] counter_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter_reg <= 4'h0;
        end else if (enable_count) begin
            counter_reg <= counter_reg + 1'b1;
        end
    end
    assign counter_val_out = counter_reg;
endmodule
module ParameterizedLogic #(
    parameter DATA_WIDTH = 16
) (
    input  logic [DATA_WIDTH-1:0] input_data_p,
    input  logic [1:0]          select_p,
    output logic [DATA_WIDTH-1:0] output_data_p
);
    localparam HALF_WIDTH = DATA_WIDTH / 2;
    logic [DATA_WIDTH-1:0] temp_output;
    always_comb begin
        case(select_p)
            2'b00: temp_output = '0;
            2'b01: temp_output = input_data_p;
            2'b10: temp_output = {{(DATA_WIDTH - HALF_WIDTH){1'b0}}, input_data_p[HALF_WIDTH-1:0]};
            2'b11: temp_output = {input_data_p[DATA_WIDTH-1:HALF_WIDTH], {(DATA_WIDTH - HALF_WIDTH){1'b0}}};
            default: temp_output = 'X;
        endcase
    end
    assign output_data_p = temp_output;
endmodule
module MemoryAccess (
    input  logic         clk_mem,
    input  logic         write_enable_mem,
    input  logic         read_enable_mem,
    input  logic [3:0]   address_mem,
    input  logic [7:0]   data_in_mem,
    output logic [7:0]   data_out_mem
);
    logic [7:0] my_ram [0:15];
    always_ff @(posedge clk_mem) begin
        if (write_enable_mem) begin
            my_ram[address_mem] <= data_in_mem;
        end
    end
    assign data_out_mem = read_enable_mem ? my_ram[address_mem] : '0;
endmodule
interface MyComplexInterface;
    logic [7:0] data_if;
    logic       valid_if;
    logic       ready_if;
    modport Producer (output data_if, output valid_if, input ready_if);
    modport Consumer (input data_if, input valid_if, output ready_if);
endinterface
class MyDataProcessor;
    logic [7:0] internal_buffer;
    function new();
        internal_buffer = '0;
    endfunction
    function logic [7:0] process_data(logic [7:0] in_data_c);
        internal_buffer = in_data_c + 8'h1;
        return internal_buffer;
    endfunction
endclass
module InterfaceClassFunctionTask (
    input  logic [7:0]                 consumer_data_if,
    input  logic                       consumer_valid_if,
    output logic                       consumer_ready_if,
    input  logic                       clk_ict,
    output logic [7:0]                 processed_result_ict,
    output logic                       calculation_done_ict
);
    logic [7:0] current_data_ict;
    logic [7:0] temp_processed_data_ict;
    MyDataProcessor data_proc_obj_ict;
    function automatic logic [7:0] multiply_by_two(logic [7:0] val_mbt);
        return val_mbt * 2;
    endfunction
    task automatic calculate_done_flag (input logic [7:0] val_cdf, output logic done_flag_cdf);
        if (val_cdf > 8'h7F) begin
            done_flag_cdf = 1'b1;
        end else begin
            done_flag_cdf = 1'b0;
        end
    endtask
    always_ff @(posedge clk_ict) begin
        if (data_proc_obj_ict == null) begin
            data_proc_obj_ict = new();
        end
        consumer_ready_if <= 1'b0;
        if (consumer_valid_if) begin
            current_data_ict = consumer_data_if;
            consumer_ready_if <= 1'b1;
            temp_processed_data_ict = data_proc_obj_ict.process_data(current_data_ict);
            processed_result_ict <= multiply_by_two(temp_processed_data_ict);
            calculate_done_flag(processed_result_ict, calculation_done_ict);
        end else begin
            processed_result_ict <= '0;
            calculation_done_ict <= 1'b0;
        end
    end
endmodule
module GenerateBlockExample (
    input  logic [1:0] sel_gen,
    input  logic [7:0] data_in_gen,
    output logic [7:0] data_out_gen
);
    logic [7:0] intermediate_values_gen [0:3];
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin : gen_block_loop
            assign intermediate_values_gen[i] = data_in_gen + i;
        end
    endgenerate
    generate
        if (1) begin : always_enabled_logic
            always_comb begin
                case (sel_gen)
                    2'b00: data_out_gen = intermediate_values_gen[0];
                    2'b01: data_out_gen = intermediate_values_gen[1];
                    2'b10: data_out_gen = intermediate_values_gen[2];
                    2'b11: data_out_gen = intermediate_values_gen[3];
                    default: data_out_gen = 'X;
                endcase
            end
        end
    endgenerate
endmodule
module DataStructuresAndCasting (
    input  logic [15:0] raw_input_data_ds,
    input  logic        use_union_select_ds,
    output logic [7:0]  extracted_byte_ds,
    output logic [7:0]  union_result_byte_ds
);
    typedef struct packed {
        logic [7:0] upper_byte;
        logic [7:0] lower_byte;
    } my_word_t;
    typedef union packed {
        logic [15:0] as_word;
        my_word_t    as_struct;
        logic [1:0][7:0] as_bytes;
    } my_union_t;
    my_word_t    word_data_var;
    my_union_t   union_data_var;
    assign word_data_var = raw_input_data_ds;
    assign extracted_byte_ds = word_data_var.lower_byte;
    always_comb begin
        union_data_var.as_word = raw_input_data_ds;
        if (use_union_select_ds) begin
            union_result_byte_ds = union_data_var.as_bytes[1];
        end else begin
            union_result_byte_ds = union_data_var.as_struct.upper_byte;
        end
    end
endmodule
module LoopExamples (
    input  logic [7:0] input_val_loop,
    input  logic       reset_loop_en,
    output logic [7:0] sum_upto_val_loop,
    output logic [3:0] count_down_result_loop
);
    logic [7:0] loop_sum_int;
    logic [3:0] current_count_int_comb;
    always_comb begin
        loop_sum_int = '0;
        for (int j = 0; j <= input_val_loop; j++) begin
            loop_sum_int = loop_sum_int + j;
        end
        sum_upto_val_loop = loop_sum_int;
    end
    always_comb begin
        current_count_int_comb = input_val_loop[3:0];
        while (current_count_int_comb > 0 && !reset_loop_en) begin
            current_count_int_comb = current_count_int_comb - 1'b1;
        end
        count_down_result_loop = current_count_int_comb;
    end
endmodule
