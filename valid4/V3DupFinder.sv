module ComplexCombinatorial #(
    parameter DATA_WIDTH = 8
) (
    input logic [DATA_WIDTH-1:0] in_a,
    input logic [DATA_WIDTH-1:0] in_b,
    input logic [DATA_WIDTH-1:0] in_c,
    input logic [DATA_WIDTH-1:0] in_d,
    input logic select_1,
    input logic select_2,
    input logic [1:0] op_sel,
    output logic [DATA_WIDTH-1:0] out_result,
    output logic                     out_status
);
    logic [DATA_WIDTH-1:0] temp_val_x;
    logic [DATA_WIDTH-1:0] temp_val_y;
    logic [DATA_WIDTH-1:0] temp_val_z;
    logic [DATA_WIDTH-1:0] intermediate_res1;
    logic [DATA_WIDTH-1:0] intermediate_res2;
    localparam ADD_OP = 2'b00;
    localparam SUB_OP = 2'b01;
    localparam MUL_OP = 2'b10;
    localparam DIV_OP = 2'b11;
    always_comb begin
        temp_val_x = '0;
        temp_val_y = '0;
        intermediate_res1 = '0;
        intermediate_res2 = '0;
        temp_val_z = '0;
        out_result = '0;
        out_status = 1'b0;
        if (select_1) begin
            temp_val_x = (in_a + in_b) - in_c;
            if (select_2) begin
                intermediate_res1 = temp_val_x * 2;
                temp_val_y = (in_d | temp_val_x) & (~in_b);
            end else begin
                intermediate_res1 = temp_val_x / 2;
                temp_val_y = (in_d ^ temp_val_x) + in_b;
            end
        end else begin
            temp_val_x = (in_a - in_b) + in_c;
            if (select_2) begin
                intermediate_res1 = temp_val_x >>> 1;
                temp_val_y = (in_d + temp_val_x) * in_b;
            end else begin
                intermediate_res1 = temp_val_x <<< 1;
                temp_val_y = (in_d - temp_val_x) / in_b;
            end
        end
        case (op_sel)
            ADD_OP: intermediate_res2 = intermediate_res1 + temp_val_y;
            SUB_OP: intermediate_res2 = intermediate_res1 - temp_val_y;
            MUL_OP: intermediate_res2 = intermediate_res1 * temp_val_y;
            DIV_OP: intermediate_res2 = intermediate_res1 / (temp_val_y == 0 ? 1 : temp_val_y);
            default: intermediate_res2 = '0;
        endcase
        temp_val_z = {1'b0, intermediate_res2[DATA_WIDTH-1:1]} | {intermediate_res2[DATA_WIDTH-2:0], 1'b0};
        out_result = temp_val_z ^ in_d;
        out_status = |out_result;
    end
endmodule
module AdvancedTypesAndLoops (
    input bit [3:0] addr,
    input byte      data_in,
    input logic     write_en,
    input logic     clk,
    input logic     reset_n,
    output logic    valid_out,
    output byte     data_out
);
    typedef enum bit [1:0] {
        IDLE,
        READ,
        WRITE,
        ERROR_STATE
    } State_e;
    typedef struct packed {
        State_e current_state;
        bit     is_valid;
        byte    value;
    } ControlData_s;
    State_e       current_fsm_state_q, next_fsm_state_n;
    byte memory_fixed_q [16];
    byte memory_dynamic_q [];
    logic [7:0] data_fifo_q [$];
    class DataPacket;
        rand bit [7:0] payload_data [8];
        logic [3:0]    packet_id;
        function new(logic [3:0] id);
            packet_id = id;
        endfunction
        function int calculate_checksum();
            int checksum = 0;
            for (int i=0; i<8; i++) begin
                checksum += payload_data[i];
            end
            return checksum;
        endfunction
    endclass
    DataPacket my_packet_q;
    logic initialized_mem_and_class_q;
    ControlData_s ctrl_reg_comb;
    function void create_dynamic_byte_array(ref byte array_ref[], int size);
        array_ref = new [size];
    endfunction
    function DataPacket create_data_packet_instance(logic [3:0] id);
        DataPacket instance;
        instance = new(id);
        return instance;
    endfunction
    always_ff @(posedge clk or negedge reset_n) begin
        int i;
        if (!reset_n) begin
            current_fsm_state_q <= IDLE;
            for (i=0; i<16; i++) memory_fixed_q[i] <= '0;
            create_dynamic_byte_array(memory_dynamic_q, 0);
            data_fifo_q <= {};
            my_packet_q <= null;
            initialized_mem_and_class_q <= 1'b0;
        end else begin
            if (!initialized_mem_and_class_q) begin
                create_dynamic_byte_array(memory_dynamic_q, 4);
                memory_dynamic_q[0] <= 8'hAA;
                memory_dynamic_q[1] <= 8'hBB;
                memory_dynamic_q[2] <= 8'hCC;
                memory_dynamic_q[3] <= 8'hDD;
                my_packet_q <= create_data_packet_instance(addr[3:0]);
                initialized_mem_and_class_q <= 1'b1;
            end
            current_fsm_state_q <= next_fsm_state_n;
            case (next_fsm_state_n)
                WRITE: begin
                    memory_fixed_q[addr] <= data_in;
                    if (addr[1:0] < memory_dynamic_q.size()) begin
                        memory_dynamic_q[addr[1:0]] <= data_in;
                    end
                    data_fifo_q.push_front(data_in);
                end
                default: begin
                end
            endcase
            for (i=0; i<4; i++) begin
                if (i == addr[1:0] && i < memory_dynamic_q.size()) begin
                    memory_dynamic_q[i] <= data_in + 1;
                end
            end
        end
    end
    always_comb begin
        next_fsm_state_n = current_fsm_state_q;
        valid_out = 1'b0;
        data_out = '0;
        ctrl_reg_comb.current_state = current_fsm_state_q;
        ctrl_reg_comb.is_valid = 1'b0;
        ctrl_reg_comb.value = '0;
        case (current_fsm_state_q)
            IDLE: begin
                if (write_en) begin
                    next_fsm_state_n = WRITE;
                end else if (addr == 4'hF) begin
                    next_fsm_state_n = READ;
                end
            end
            WRITE: begin
                valid_out = 1'b1;
                data_out = data_in;
                next_fsm_state_n = IDLE;
            end
            READ: begin
                data_out = memory_fixed_q[addr];
                valid_out = 1'b1;
                next_fsm_state_n = IDLE;
            end
            default: begin
                next_fsm_state_n = ERROR_STATE;
            end
        endcase
        ctrl_reg_comb.current_state = current_fsm_state_q;
        ctrl_reg_comb.is_valid = valid_out;
        ctrl_reg_comb.value = data_out;
        if (my_packet_q != null) begin
             int chksum = my_packet_q.calculate_checksum();
             logic [7:0] dummy = chksum;
        end
    end
endmodule
interface MySimpleInterface (
    input bit clk,
    input bit reset_n
);
    logic [7:0] data_tx;
    logic [7:0] data_rx;
    logic       request;
    logic       grant;
    modport Master (output data_tx, output request, input data_rx, input grant, input clk, input reset_n);
    modport Slave  (input data_tx, input request, output data_rx, output grant, input clk, input reset_n);
endinterface
module InterfaceUser (
    MySimpleInterface.Master  master_if,
    input logic [7:0]         input_data,
    input logic               send_request,
    output logic [7:0]        output_data_echo,
    output logic              request_sent_ack
);
    logic [7:0] internal_buffer_tx;
    logic [7:0] internal_buffer_rx;
    logic       internal_request_status;
    always_comb begin
        master_if.data_tx = input_data;
        master_if.request = send_request;
        internal_buffer_rx = master_if.data_rx;
        internal_request_status = master_if.grant;
        output_data_echo = '0;
        request_sent_ack = 1'b0;
        if (master_if.grant && master_if.request) begin
            output_data_echo = master_if.data_rx ^ master_if.data_tx;
            request_sent_ack = 1'b1;
        end
    end
    typedef struct packed {
        logic [3:0] header;
        logic [3:0] checksum;
    } PacketHeader_t;
    PacketHeader_t my_packet_header;
    logic [7:0] combined_data;
    always_comb begin
        my_packet_header.header = master_if.data_tx[7:4];
        my_packet_header.checksum = master_if.data_tx[3:0];
        combined_data = {my_packet_header.header, my_packet_header.checksum};
        internal_buffer_tx = '0;
        if (combined_data == 8'hFF) begin
            internal_buffer_tx = combined_data - 1;
        end else if (combined_data == 8'h00) begin
            internal_buffer_tx = combined_data + 1;
        end else begin
            internal_buffer_tx = combined_data;
        end
    end
endmodule
module StateMachineLogic (
    input logic clk,
    input logic reset_n,
    input logic start_task,
    output logic done_task,
    output logic [3:0] current_state_out
);
    typedef enum logic [3:0] {
        STATE_IDLE,
        STATE_INIT,
        STATE_PROCESSING,
        STATE_DONE,
        STATE_ERROR
    } FSM_State_e;
    FSM_State_e current_state_q, next_state_n;
    logic [3:0] counter_q;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            current_state_q <= STATE_IDLE;
            counter_q <= '0;
            done_task <= 1'b0;
        end else begin
            current_state_q <= next_state_n;
            if (next_state_n == STATE_PROCESSING) begin
                counter_q <= counter_q + 1;
            end else if (next_state_n == STATE_IDLE) begin
                counter_q <= '0;
            end
            done_task <= (next_state_n == STATE_DONE);
        end
    end
    always_comb begin
        next_state_n = current_state_q;
        current_state_out = current_state_q;
        case (current_state_q)
            STATE_IDLE: begin
                if (start_task) begin
                    next_state_n = STATE_INIT;
                end
            end
            STATE_INIT: begin
                next_state_n = STATE_PROCESSING;
            end
            STATE_PROCESSING: begin
                if (counter_q == 4'd10) begin
                    next_state_n = STATE_DONE;
                end else if (counter_q > 4'd10) begin
                    next_state_n = STATE_ERROR;
                end
            end
            STATE_DONE: begin
                if (!start_task) begin
                    next_state_n = STATE_IDLE;
                end
            end
            STATE_ERROR: begin
                next_state_n = STATE_ERROR;
            end
            default: begin
                next_state_n = STATE_ERROR;
            end
        endcase
    end
endmodule
module ParamLogicGenerator #(
    parameter NUM_SECTIONS = 2,
    parameter DATA_BIT = 4
) (
    input logic [NUM_SECTIONS*DATA_BIT-1:0] input_vec,
    output logic [NUM_SECTIONS*DATA_BIT-1:0] output_vec
);
    genvar i;
    generate
        for (i = 0; i < NUM_SECTIONS; i++) begin : section_gen
            logic [DATA_BIT-1:0] current_input = input_vec[ (i*DATA_BIT) +: DATA_BIT ];
            logic [DATA_BIT-1:0] processed_data;
            always_comb begin
                processed_data = '0;
                if (i % 2 == 0) begin
                    processed_data = current_input + (DATA_BIT'(i+1));
                    if (current_input[0] == 1'b1) begin
                        processed_data = processed_data ^ current_input;
                    end
                end else begin
                    processed_data = current_input - (DATA_BIT'(i+1));
                    if (current_input[0] == 1'b0) begin
                        processed_data = processed_data | current_input;
                    end
                end
                output_vec[ (i*DATA_BIT) +: DATA_BIT ] = processed_data;
            end
        end
    endgenerate
    logic [DATA_BIT-1:0] extra_val;
    logic [DATA_BIT-1:0] temp_sum;
    always_comb begin
        temp_sum = '0;
        for (int k = 0; k < NUM_SECTIONS; k++) begin
            temp_sum = temp_sum + input_vec[ (k*DATA_BIT) +: DATA_BIT ];
        end
        extra_val = temp_sum >>> 2;
    end
    logic [DATA_BIT-1:0] last_output;
    assign last_output = extra_val + output_vec[0 +: DATA_BIT];
endmodule
module AdvancedArrays (
    input logic [7:0] val_in,
    input logic [3:0] index_in,
    input logic       add_val,
    input logic       clk,
    input logic       reset_n,
    output logic [7:0] val_out,
    output int         queue_size_out
);
    logic [7:0] fixed_array_q[16];
    logic [7:0] dynamic_array_q[];
    logic [7:0] data_queue_q[$];
    logic [7:0] assoc_array_q[string];
    logic initialized_arrays_q;
    string current_key_comb;
    function void create_dynamic_array(ref logic [7:0] array_ref[], int size);
        array_ref = new [size];
    endfunction
    always_ff @(posedge clk or negedge reset_n) begin
        int i;
        if (!reset_n) begin
            for (i=0; i<16; i++) fixed_array_q[i] <= '0;
            create_dynamic_array(dynamic_array_q, 0);
            data_queue_q <= {};
            assoc_array_q.delete;
            initialized_arrays_q <= 1'b0;
        end else begin
            if (!initialized_arrays_q) begin
                create_dynamic_array(dynamic_array_q, 8);
                for (i=0; i<8; i++) begin
                    dynamic_array_q[i] <= 8'hFF - i;
                end
                assoc_array_q["key1"] <= 8'hA1;
                assoc_array_q["key_two"] <= 8'hB2;
                assoc_array_q["another_key"] <= 8'hC3;
                initialized_arrays_q <= 1'b1;
            end
            if (add_val) begin
                fixed_array_q[index_in] <= val_in + 1;
                data_queue_q.push_back(val_in);
            end else begin
                fixed_array_q[index_in] <= val_in - 1;
                if (data_queue_q.size() > 0) begin
                    logic [7:0] dummy_pop_val;
                    dummy_pop_val = data_queue_q.pop_front();
                end
            end
        end
    end
    always_comb begin
        val_out = '0;
        queue_size_out = 0;
        current_key_comb = "key1";
        val_out = fixed_array_q[index_in];
        if (index_in < dynamic_array_q.size()) begin
            val_out = val_out ^ dynamic_array_q[index_in];
        end
        queue_size_out = data_queue_q.size();
        if (index_in % 2 == 0) begin
            current_key_comb = "key_two";
        end
        if (assoc_array_q.exists(current_key_comb)) begin
            val_out = val_out + assoc_array_q[current_key_comb];
        end
    end
endmodule
module RealAndIntegerMath (
    input real      real_in_a,
    input real      real_in_b,
    input int       int_in_x,
    input int       int_in_y,
    output real     real_out_sum,
    output int      int_out_product
);
    real temp_real_val_1;
    real temp_real_val_2;
    int  temp_int_val_1;
    int  temp_int_val_2;
    always_comb begin
        real_out_sum = '0;
        int_out_product = '0;
        temp_real_val_1 = '0;
        temp_real_val_2 = '0;
        temp_int_val_1 = '0;
        temp_int_val_2 = '0;
        real_out_sum = real_in_a + real_in_b;
        real_out_sum = real_out_sum * real_in_b / 2.0;
        real_out_sum = $sqrt(real_out_sum);
        real_out_sum = real_out_sum + $ln(real_in_a);
        real_out_sum = real_out_sum - $exp(real_in_b);
        temp_int_val_1 = int_in_x + int_in_y;
        temp_int_val_2 = int_in_x << 2 | int_in_y >> 1;
        int_out_product = temp_int_val_1 * temp_int_val_2;
        int_out_product = int_out_product & (~int_in_x);
        int_out_product = (int_in_x > int_in_y) ? int_out_product + int_in_x : int_out_product - int_in_y;
    end
endmodule
module RandomClassUsage (
    input logic [7:0] input_seed_val,
    input logic       enable_rand,
    input logic       clk,
    input logic       reset_n,
    output logic [7:0] random_output,
    output int         constraint_sum_out
);
    class RandomData;
        rand int value_a;
        rand int value_b;
        rand int value_c;
        constraint c_range {
            value_a inside {[1:100]};
            value_b inside {[10:200]};
            value_c == value_a + value_b;
            value_c < 300;
        }
        function int get_sum();
            return value_a + value_b + value_c;
        endfunction
    endclass
    RandomData my_rand_data_q;
    logic initialized_rand_class_q;
    logic [7:0] current_rand_val_comb;
    int         current_sum_comb;
    function RandomData create_random_data_instance();
        RandomData instance;
        instance = new();
        return instance;
    endfunction
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            my_rand_data_q <= null;
            initialized_rand_class_q <= 1'b0;
        end else begin
            if (!initialized_rand_class_q) begin
                my_rand_data_q <= create_random_data_instance();
                initialized_rand_class_q <= 1'b1;
            end
        end
    end
    always_comb begin
        random_output = '0;
        constraint_sum_out = 0;
        current_rand_val_comb = '0;
        current_sum_comb = 0;
        if (enable_rand) begin
            if (my_rand_data_q != null) begin
                int rand_success;
                rand_success = my_rand_data_q.randomize() with { value_a > input_seed_val; };
                current_rand_val_comb = my_rand_data_q.value_a[7:0];
                current_sum_comb = my_rand_data_q.get_sum();
            end else begin
                current_rand_val_comb = '0;
                current_sum_comb = 0;
            end
        end else begin
            current_rand_val_comb = input_seed_val;
            current_sum_comb = 0;
        end
        random_output = current_rand_val_comb;
        constraint_sum_out = current_sum_comb;
    end
endmodule
