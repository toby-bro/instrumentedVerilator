interface SimpleBus_if (input logic clk, input logic rst_n);
    logic [31:0] addr;
    logic [31:0] wdata;
    logic [31:0] rdata;
    logic        write_en;
    logic        read_en;
    modport Master (output addr, output wdata, output write_en, output read_en, input rdata, input clk, input rst_n);
    modport Slave  (input addr, input wdata, input write_en, input read_en, output rdata, input clk, input rst_n);
endinterface
module ModCombinational (
    input  logic [7:0] in_data_comb,
    input  logic       in_sel_comb,
    output logic [7:0] out_result_comb
);
    logic [7:0] temp_comb_a, temp_comb_b;
    byte        b_val;
    int         i_val;
    real        r_val;
    always_comb begin
        temp_comb_a = in_data_comb + 8'd10;
        temp_comb_b = in_data_comb - 8'd5;
        if (in_sel_comb) begin
            out_result_comb = temp_comb_a;
        end else begin
            out_result_comb = temp_comb_b;
        end
        b_val = temp_comb_a[7:0];
        i_val = temp_comb_b;
        r_val = $itor(i_val) / 2.0;
    end
    logic [7:0] out_direct;
    assign out_direct = in_data_comb | {8{in_sel_comb}};
endmodule
module ModSequential (
    input  logic       clk_seq,
    input  logic       rst_n_seq,
    input  logic [3:0] in_load_seq,
    output logic [3:0] out_counter_seq
);
    logic [3:0] counter_reg;
    enum {STATE_IDLE, STATE_COUNT} fsm_state, next_fsm_state;
    always_ff @(posedge clk_seq or negedge rst_n_seq) begin
        if (!rst_n_seq) begin
            counter_reg <= 4'd0;
            fsm_state <= STATE_IDLE;
        end else begin
            counter_reg <= in_load_seq;
            fsm_state <= next_fsm_state;
        end
    end
    always_comb begin
        next_fsm_state = fsm_state;
        unique case (fsm_state)
            STATE_IDLE:
                if (in_load_seq != 4'd0) begin
                    next_fsm_state = STATE_COUNT;
                end
            STATE_COUNT:
                if (counter_reg == 4'd15) begin
                    next_fsm_state = STATE_IDLE;
                end
            default: next_fsm_state = STATE_IDLE;
        endcase
    end
    assign out_counter_seq = counter_reg;
endmodule
module ModComplexLogic (
    input  logic [15:0] in_address,
    input  logic [31:0] in_write_data,
    input  logic        in_write_en,
    output logic [31:0] out_read_data
);
    typedef struct packed {
        logic [7:0] opcode;
        logic [7:0] addr_mode;
        logic [15:0] operand;
    } Instruction_t;
    Instruction_t current_instr;
    logic [31:0] memory [0:255];
    logic [7:0] byte_mem [256];
    logic [3:0][3:0] packed_matrix;
    int data_store_assoc_array [*];
    always_comb begin
        current_instr.opcode = in_write_data[31:24];
        current_instr.addr_mode = in_write_data[23:16];
        current_instr.operand = in_write_data[15:0];
        if (in_write_en) begin
            if (in_address < 16'h100) begin
                memory[in_address] = in_write_data;
                byte_mem[in_address[7:0]] = in_write_data[7:0];
            end else if (in_address >= 16'h1000 && in_address < 16'h2000) begin
                data_store_assoc_array[in_address] = $signed(in_write_data);
            end
        end
        if (in_address < 16'h100) begin
            out_read_data = memory[in_address];
        end else if (in_address >= 16'h1000 && in_address < 16'h2000) begin
            if (data_store_assoc_array.exists(in_address)) begin
                out_read_data = $unsigned(data_store_assoc_array[in_address]);
            end else begin
                out_read_data = 32'hDEADBEEF;
            end
        end else begin
            out_read_data = 32'h0;
        end
        packed_matrix = '0;
        packed_matrix[0][0] = in_address[0];
    end
endmodule
module ModClassExample (
    input  logic       clk_class,
    input  logic       reset_class,
    input  logic [7:0] in_value_class,
    output logic [7:0] out_processed_class
);
    class MyDataProcessor;
        local int data_reg;
        int counter;
        function new();
            data_reg = 0;
            counter = 0;
        endfunction
        function int process(int input_val);
            data_reg = input_val + 1;
            counter++;
            return data_reg;
        endfunction
        function void set_data(int val);
            this.data_reg = val;
        endfunction
        function int get_data();
            return data_reg;
        endfunction
    endclass
    MyDataProcessor processor_inst;
    always_ff @(posedge clk_class or posedge reset_class) begin
        if (reset_class) begin
            processor_inst = new();
            out_processed_class <= 8'd0;
        end else begin
            if (processor_inst == null) begin
                processor_inst = new();
            end
            out_processed_class <= processor_inst.process(in_value_class);
        end
    end
endmodule
module ModDPI (
    input  int in_a_dpi,
    input  int in_b_dpi,
    output int out_sum_dpi
);
    import "DPI-C" function int c_add_integers (int a, int b);
    always_comb begin
        out_sum_dpi = c_add_integers(in_a_dpi, in_b_dpi);
    end
endmodule
module ModRandomization (
    input  logic clk_rand,
    input  logic reset_rand,
    output int   out_random_val
);
    class Randomizer;
        rand int rand_num;
        randc logic [3:0] rand_cycle;
        constraint c_rand_num {
            rand_num inside {[10:100]};
            rand_num % 2 == 0;
        }
        constraint c_rand_cycle {
            rand_cycle != 4'd0;
        }
    endclass
    Randomizer rand_obj;
    always_ff @(posedge clk_rand or posedge reset_rand) begin
        if (reset_rand) begin
            rand_obj = new();
            out_random_val <= 0;
        end else begin
            if (rand_obj == null) begin
                rand_obj = new();
            end
            if (rand_obj.randomize()) begin
                out_random_val <= rand_obj.rand_num + rand_obj.rand_cycle;
            end else begin
                out_random_val <= -1;
            end
        end
    end
endmodule
module ModAssertions (
    input  logic clk_assert,
    input  logic reset_assert,
    input  logic a_assert,
    input  logic b_assert,
    output logic out_flag_assert
);
    always_comb begin
        assert (a_assert || b_assert)
        else $error("Assertion Failed: Both A and B are low!");
        out_flag_assert = a_assert && b_assert;
    end
endmodule
module ModGenerate (
    input  logic [7:0] in_gen_data,
    input  logic [2:0] in_select_gen,
    output logic [7:0] out_gen_result
);
    parameter NUM_ADDERS = 4;
    logic [7:0] intermediate_sum [NUM_ADDERS-1:0];
    genvar i;
    generate
        for (i = 0; i < NUM_ADDERS; i = i + 1) begin : add_stage
            if (i == 0) begin : first_stage
                assign intermediate_sum[i] = in_gen_data + 8'd1;
            end else begin : subsequent_stage
                assign intermediate_sum[i] = intermediate_sum[i-1] + (i * 2);
            end
        end
    endgenerate
    always_comb begin
        case (in_select_gen)
            0: out_gen_result = intermediate_sum[0];
            1: out_gen_result = intermediate_sum[1];
            2: out_gen_result = intermediate_sum[2];
            3: out_gen_result = intermediate_sum[3];
            default: out_gen_result = 8'hFF;
        endcase
    end
endmodule
module ModInterfaceUser (
    SimpleBus_if.Master bus_master_mp,
    output logic [7:0]   out_status_code
);
    logic [31:0] internal_data;
    always_comb begin
        bus_master_mp.addr = 32'h1000;
        bus_master_mp.wdata = internal_data;
        bus_master_mp.write_en = bus_master_mp.clk;
        bus_master_mp.read_en = ~bus_master_mp.clk;
        internal_data = bus_master_mp.rdata + 32'd1;
        out_status_code = bus_master_mp.addr[7:0] ^ bus_master_mp.rdata[7:0];
    end
endmodule
module ModParameterized #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH      = 4
) (
    input  logic [DATA_WIDTH-1:0] in_param_data,
    input  logic                  in_param_sel,
    output logic [DATA_WIDTH-1:0] out_param_result
);
    logic [DATA_WIDTH-1:0] temp_array [DEPTH-1:0];
    genvar idx;
    generate
        for (idx = 0; idx < DEPTH; idx++) begin : param_sum
            if (idx == 0) begin
                assign temp_array[idx] = in_param_data;
            end else begin
                assign temp_array[idx] = temp_array[idx-1] + in_param_data;
            end
        end
    endgenerate
    always_comb begin
        if (in_param_sel) begin
            out_param_result = temp_array[DEPTH-1];
        end else begin
            out_param_result = temp_array[0];
        end
    end
endmodule
module ModFuncTask (
    input  logic [7:0] in_val_ft,
    input  logic       in_trigger_ft,
    output logic [7:0] out_val_ft
);
    function automatic logic [7:0] my_func(logic [7:0] data);
        return data + 8'd1;
    endfunction
    task my_task(input logic [7:0] val_in, output logic [7:0] val_out);
        val_out = val_in * 2;
    endtask
    logic [7:0] task_result;
    always_comb begin
        if (in_trigger_ft) begin
            out_val_ft = my_func(in_val_ft);
            my_task(in_val_ft, task_result);
        end else begin
            out_val_ft = in_val_ft;
            task_result = 0;
        end
    end
endmodule
module ModLocalParamConst (
    input  logic [7:0] in_data_lpc,
    output logic [7:0] out_data_lpc
);
    localparam ADD_VALUE = 8'd5;
    const logic [7:0] MULT_FACTOR = 8'd2;
    assign out_data_lpc = (in_data_lpc + ADD_VALUE) * MULT_FACTOR;
endmodule
module ModUnion (
    input  logic [31:0] in_union_data,
    input  logic        in_union_sel,
    output logic [31:0] out_union_result
);
    typedef union packed {
        logic [31:0] full_word;
        struct packed {
            logic [15:0] low_half;
            logic [15:0] high_half;
        } halves;
        struct packed {
            logic [7:0] byte0;
            logic [7:0] byte1;
            logic [7:0] byte2;
            logic [7:0] byte3;
        } bytes;
    } WordOrBytes_t;
    WordOrBytes_t my_union;
    always_comb begin
        my_union.full_word = in_union_data;
        if (in_union_sel) begin
            out_union_result = {my_union.halves.high_half, my_union.halves.low_half};
        end else begin
            out_union_result = {my_union.bytes.byte3, my_union.bytes.byte2, my_union.bytes.byte1, my_union.bytes.byte0};
        end
    end
endmodule
module ModQueue (
    input  logic [7:0] in_push_data,
    input  logic       in_push_en,
    input  logic       in_pop_en,
    output logic [7:0] out_pop_data,
    output int         out_queue_size
);
    logic [7:0] data_q [$];
    always_comb begin
        if (in_push_en) begin
            data_q.push_back(in_push_data);
        end
        if (in_pop_en && data_q.size() > 0) begin
            out_pop_data = data_q.pop_front();
        end else begin
            out_pop_data = 8'hXX;
        end
        out_queue_size = data_q.size();
    end
endmodule
module ModDynamicArray (
    input  logic [7:0] in_data_da,
    input  int         in_size_da,
    output logic [7:0] out_sum_da
);
    logic [7:0] dyn_arr [];
    always_comb begin
        dyn_arr = new [in_size_da];
        out_sum_da = 8'd0;
        for (int k = 0; k < in_size_da; k++) begin
            dyn_arr[k] = in_data_da + k;
            out_sum_da += dyn_arr[k];
        end
    end
endmodule
module ModBitStreamCast (
    input  logic [31:0] in_bit_data,
    input  logic        in_cast_sel,
    output int          out_cast_int,
    output real         out_cast_real
);
    struct packed {
        logic [15:0] val1;
        logic [15:0] val2;
    } s_packed;
    always_comb begin
        s_packed = in_bit_data;
        if (in_cast_sel) begin
            out_cast_int = int'(s_packed);
            out_cast_real = real'(s_packed.val1);
        end else begin
            out_cast_int = int'(in_bit_data);
            out_cast_real = $itor(in_bit_data);
        end
    end
endmodule
module TopLevelWrapper (
    input logic clk,
    input logic rst_n,
    input logic [7:0] data_in,
    output logic [7:0] result_out
);
    logic [7:0] comb_out, gen_out, func_task_out, lpc_out, queue_out_data;
    logic [31:0] complex_read_out, param_out_large, union_out_data;
    logic [7:0] dynamic_array_sum;
    int dpi_func_out, rand_val_check, queue_size, bit_stream_int_out;
    logic [7:0] class_proc_out, if_status;
    logic [3:0] seq_out;
    logic assertion_pass_flag;
    real bit_stream_real_out;
    SimpleBus_if bus_connection (.*);
    ModCombinational u_comb (
        .in_data_comb (data_in),
        .in_sel_comb  (rst_n),
        .out_result_comb(comb_out)
    );
    ModSequential u_seq (
        .clk_seq (clk),
        .rst_n_seq(rst_n),
        .in_load_seq(4'd1),
        .out_counter_seq(seq_out)
    );
    ModComplexLogic u_complex (
        .in_address(16'h10),
        .in_write_data({data_in, data_in, data_in, data_in}),
        .in_write_en(rst_n),
        .out_read_data(complex_read_out)
    );
    ModClassExample u_class (
        .clk_class(clk),
        .reset_class(~rst_n),
        .in_value_class(data_in),
        .out_processed_class(class_proc_out)
    );
    ModDPI u_dpi (
        .in_a_dpi(8),
        .in_b_dpi(data_in),
        .out_sum_dpi(dpi_func_out)
    );
    ModRandomization u_rand (
        .clk_rand(clk),
        .reset_rand(~rst_n),
        .out_random_val(rand_val_check)
    );
    ModAssertions u_assert (
        .clk_assert(clk),
        .reset_assert(~rst_n),
        .a_assert(data_in[0]),
        .b_assert(data_in[1]),
        .out_flag_assert(assertion_pass_flag)
    );
    ModGenerate u_gen (
        .in_gen_data(data_in),
        .in_select_gen(seq_out[2:0]),
        .out_gen_result(gen_out)
    );
    ModInterfaceUser u_if_user (
        .bus_master_mp(bus_connection.Master),
        .out_status_code(if_status)
    );
    ModParameterized #(.DATA_WIDTH(16), .DEPTH(8)) u_param_large (
        .in_param_data({8'h0, data_in}),
        .in_param_sel(rst_n),
        .out_param_result(param_out_large[15:0])
    );
    ModFuncTask u_ft (
        .in_val_ft(data_in),
        .in_trigger_ft(rst_n),
        .out_val_ft(func_task_out)
    );
    ModLocalParamConst u_lpc (
        .in_data_lpc(data_in),
        .out_data_lpc(lpc_out)
    );
    ModUnion u_union (
        .in_union_data({data_in, data_in, data_in, data_in}),
        .in_union_sel(rst_n),
        .out_union_result(union_out_data)
    );
    ModQueue u_queue (
        .in_push_data(data_in),
        .in_push_en(rst_n),
        .in_pop_en(~rst_n),
        .out_pop_data(queue_out_data),
        .out_queue_size(queue_size)
    );
    ModDynamicArray u_da (
        .in_data_da(data_in),
        .in_size_da(data_in[2:0]),
        .out_sum_da(dynamic_array_sum)
    );
    ModBitStreamCast u_bsc (
        .in_bit_data({data_in, data_in, data_in, data_in}),
        .in_cast_sel(rst_n),
        .out_cast_int(bit_stream_int_out),
        .out_cast_real(bit_stream_real_out)
    );
    assign result_out = comb_out + gen_out + class_proc_out + if_status + func_task_out + lpc_out + queue_out_data + dynamic_array_sum + bit_stream_int_out[7:0];
endmodule
