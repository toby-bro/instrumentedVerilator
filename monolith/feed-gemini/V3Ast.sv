module AstNode_Module1 (
    input logic [31:0] in_val1,
    input logic [31:0] in_val2,
    output logic [63:0] out_result1
);
    logic [63:0] sum_reg;
    logic [31:0] diff_wire;
    logic signed [15:0] signed_a;
    logic signed [15:0] signed_b;
    logic signed [31:0] signed_result;
    logic       [7:0] byte_var;
    logic [7:0] array_var[4];
    logic long_name_with_underscores_and_numbers_123;
    logic __PVT__internal_signal__DOT__nested_path;
    logic __BRA__bracketed_name__KET__;
    logic __02Dnegative_number_id;
    logic __05Funderscore_escape;
    assign long_name_with_underscores_and_numbers_123 = 1'b1;
    assign __PVT__internal_signal__DOT__nested_path = long_name_with_underscores_and_numbers_123;
    assign __BRA__bracketed_name__KET__ = __PVT__internal_signal__DOT__nested_path;
    assign __02Dnegative_number_id = __BRA__bracketed_name__KET__;
    assign __05Funderscore_escape = __02Dnegative_number_id;
    always_comb begin
        sum_reg = {in_val1, in_val2};
        diff_wire = in_val1 - in_val2;
        signed_a = 16'shABCD;
        signed_b = 16'sh1234;
        signed_result = signed_a * signed_b;
        out_result1 = sum_reg;
        out_result1 = out_result1 + signed_result;
        out_result1 = out_result1 ^ {32'h0, diff_wire};
        byte_var = 8'hFF;
        array_var[0] = byte_var;
        array_var[1] = byte_var + 1;
        array_var[2] = byte_var - 2;
        array_var[3] = byte_var * 3;
    end
endmodule
module AstNode_Module2 (
    input logic [7:0]  ctrl_in,
    input logic [15:0] data_in,
    output logic [15:0] data_out
);
    typedef struct packed {
        logic [3:0] field_a;
        logic [3:0] field_b;
    } my_packed_struct_t;
    typedef enum logic [1:0] {
        STATE_IDLE,
        STATE_ACTIVE,
        STATE_DONE
    } fsm_state_t;
    always_comb begin
        automatic my_packed_struct_t current_struct;
        automatic fsm_state_t current_state;
        automatic int loop_idx;
        automatic logic [15:0] temp_data;
        automatic string my_string;
        temp_data = 16'b0;
        loop_idx = 0;
        current_state = STATE_IDLE;
        if (ctrl_in[0]) begin
            temp_data = data_in + 1;
        end else if (ctrl_in[1]) begin
            temp_data = data_in - 1;
            current_state = STATE_ACTIVE;
        end else begin
            temp_data = data_in;
        end
        case (ctrl_in[2:1])
            2'b00: begin
                temp_data = temp_data & 16'hAAAA;
            end
            2'b01: begin
                temp_data = temp_data | 16'h5555;
            end
            2'b10: begin
                temp_data = temp_data ^ 16'hFFFF;
            end
            default: begin
                temp_data = temp_data;
                current_state = STATE_DONE;
            end
        endcase
        for (loop_idx = 0; loop_idx < 4; loop_idx = loop_idx + 1) begin
            temp_data[loop_idx] = temp_data[loop_idx] ^ data_in[loop_idx];
        end
        current_struct.field_a = ctrl_in[3:0];
        current_struct.field_b = ctrl_in[7:4];
        data_out = temp_data + current_struct;
    end
endmodule
module AstNode_Module3 (
    input logic [7:0] addr,
    input logic       write_en,
    input logic [31:0] write_data,
    input logic       clk,
    output logic [31:0] read_data
);
    class MyBaseClass;
        rand int base_val;
        function new(int val = 0);
            base_val = val;
        endfunction
        virtual function int get_val();
            return base_val;
        endfunction
    endclass
    class MyDerivedClass extends MyBaseClass;
        rand int derived_val;
        function new(int val1 = 0, int val2 = 0);
            super.new(val1);
            derived_val = val2;
        endfunction
        virtual function int get_val();
            return super.get_val() + derived_val;
        endfunction
    endclass
    virtual class AbstractClass;
        pure virtual function void do_something();
    endclass
    class ConcreteClass extends AbstractClass;
        function void do_something(); endfunction
    endclass
    MyBaseClass base_obj;
    MyDerivedClass derived_obj;
    MyBaseClass poly_obj;
    int dynamic_array[];
    int my_queue[$];
    logic [31:0] mem [255:0];
    function void process_data (input int in_d, output int out_d);
        out_d = in_d * 2;
    endfunction
    task store_and_retrieve(input logic [7:0] address, input logic [31:0] data_in_task, output logic [31:0] data_out_task);
        if (write_en) begin
            mem[address] = data_in_task;
        end
        data_out_task = mem[address];
    endtask
    always_ff @(posedge write_en or posedge clk) begin
        automatic int processed;
        automatic logic [31:0] task_read_data;
        base_obj = new(10);
        derived_obj = new(5, 15);
        if (addr == 8'h0) begin
            poly_obj = base_obj;
        end else begin
            poly_obj = derived_obj;
        end
        read_data = poly_obj.get_val();
        if (dynamic_array.size() == 0) dynamic_array = new[2];
        dynamic_array[0] = 100;
        dynamic_array[1] = 200;
        my_queue.push_back(addr);
        my_queue.push_front(write_data);
        if (my_queue.size() > 2) my_queue.pop_back();
        process_data(read_data, processed);
        read_data = processed;
        store_and_retrieve(addr, write_data, task_read_data);
        read_data = task_read_data;
    end
endmodule
module AstNode_Module4 #(
    parameter WIDTH = 8,
    parameter SIGNED_MODE = 0
) (
    input logic [WIDTH-1:0] in_a,
    input logic [WIDTH-1:0] in_b,
    output logic [WIDTH-1:0] out_c,
    output logic [WIDTH-1:0] out_proc
);
    logic [WIDTH-1:0] local_wire_1;
    logic [WIDTH-1:0] local_wire_2;
    assign local_wire_1 = in_a & in_b;
    assign local_wire_2 = in_a | in_b;
    assign out_c = (WIDTH > 16) ? (local_wire_1 + local_wire_2) : (local_wire_1 ^ local_wire_2);
    always_comb begin
        automatic logic [WIDTH-1:0] temp_a = in_a;
        automatic logic [WIDTH-1:0] temp_b = in_b;
        automatic logic [WIDTH-1:0] temp_result;
        if (SIGNED_MODE == 1) begin
            temp_result = $signed(temp_a) + $signed(temp_b);
        end else begin
            temp_result = temp_a + temp_b;
        end
        out_proc = temp_result;
        out_proc = out_proc + temp_result;
        out_proc = out_proc + temp_result;
    end
    always_comb begin
        automatic bit [3:0] small_int;
        automatic logic [7:0] big_int = 8'd200;
        small_int = big_int;
    end
endmodule
interface MyInterface (input logic clk);
    logic [31:0] data;
    logic        valid;
    logic        ready;
    modport MASTER (output data, output valid, input ready, input clk);
    modport SLAVE (input data, input valid, output ready, input clk);
endinterface
module AstNode_Module5 (
    input logic clk,
    output logic [31:0] final_result
);
    MyInterface internal_if (.clk(clk));
    logic [31:0] slave_data_in;
    int array_of_queues[2][$];
    typedef struct {
        int addr;
        int value;
    } s_mem_op_t;
    typedef union {
        int u_int_val;
        byte u_byte_arr[4];
    } u_data_t;
    always_ff @(posedge clk) begin : block_ff_m5
        automatic int local_var_1 = 0;
        automatic int local_var_2 = 0;
        automatic s_mem_op_t current_op;
        automatic u_data_t current_u_data;
        fork : fj_block_1
            begin
                local_var_1 = 1;
                internal_if.MASTER.data = 32'hFEEDFACE;
                internal_if.MASTER.valid = 1'b1;
            end
            begin
                local_var_2 = 2;
                internal_if.SLAVE.ready = 1'b1;
            end
        join_all;
        fork : fj_block_2
            begin
                local_var_1 = local_var_1 + 10;
            end
            begin
                local_var_2 = local_var_2 + 20;
            end
        join_any;
        fork : fj_block_3
            begin
                local_var_1 = local_var_1 + 100;
            end
            begin
                local_var_2 = local_var_2 + 200;
            end
        join_none;
        current_op.addr = local_var_1;
        current_op.value = local_var_2;
        current_u_data.u_int_val = current_op.addr + current_op.value;
        slave_data_in = internal_if.SLAVE.data;
        final_result = internal_if.MASTER.data + slave_data_in + current_u_data.u_int_val;
    end
    int queue_of_int_queues[string][$];
    always_comb begin : block_comb_m5
        automatic int val;
        automatic int popped_val;
        automatic int assoc_val;
        array_of_queues[0].push_back(100);
        array_of_queues[0].push_back(200);
        array_of_queues[1].push_front(300);
        if (array_of_queues[0].size() != 0) begin
            val = array_of_queues[0][0];
        end
        if (array_of_queues[0].size() > 1) begin
            popped_val = array_of_queues[0].pop_front();
        end
        queue_of_int_queues["first"].push_back(1);
        queue_of_int_queues["second"].push_back(2);
        assoc_val = queue_of_int_queues["first"][0];
    end
    inner_module inner_inst (
        .master_port(internal_if.MASTER),
        .slave_port(internal_if.SLAVE)
    );
endmodule
module inner_module (
    MyInterface.MASTER master_port,
    MyInterface.SLAVE  slave_port
);
    logic [31:0] intermediate_data;
    assign master_port.data = slave_port.data * 2;
    assign master_port.valid = slave_port.valid;
    assign slave_port.ready = master_port.ready;
    always_ff @(posedge master_port.clk) begin
        intermediate_data = master_port.data + slave_port.data;
    end
endmodule
module AstNode_Module6 (
    input logic [7:0] cmd_in,
    input logic [63:0] stream_data_in,
    output logic [63:0] stream_data_out
);
    class BasePacket;
        virtual function int get_id(); return 0; endfunction
    endclass
    class DataPacket extends BasePacket;
        int id = 1;
        function int get_id(); return id; endfunction
    endclass
    class CmdPacket extends BasePacket;
        int id = 2;
        function int get_id(); return id; endfunction
    endclass
    virtual class AbstractClass;
        pure virtual function void do_something();
    endclass
    class ConcreteClass extends AbstractClass;
        function void do_something(); endfunction
    endclass
    BasePacket base_pkt;
    DataPacket data_pkt;
    CmdPacket  cmd_pkt;
    logic [15:0] s_a = 16'h1234;
    logic [15:0] s_b = 16'h5678;
    logic [31:0] packed_stream_data;
    logic [31:0] unpacked_stream_data;
    always_comb begin
        automatic logic [7:0] temp_unpacked_arr[8];
        for (int i=0; i<8; i++) temp_unpacked_arr[i] = stream_data_in[i*8 +: 8];
        data_pkt = new();
        cmd_pkt = new();
        if (cmd_in == 8'h1) begin
            base_pkt = data_pkt;
        end else begin
            base_pkt = cmd_pkt;
        end
        stream_data_out = base_pkt.get_id();
        packed_stream_data = {<<{s_a, s_b}};
        unpacked_stream_data = {>>{temp_unpacked_arr with [0:2]}};
        stream_data_out = stream_data_in + packed_stream_data;
        stream_data_out = stream_data_out + unpacked_stream_data;
    end
endmodule
module AstNode_Module7 (
    input logic [1:0]  sel,
    input logic [7:0]  data_in_7,
    output logic [15:0] result_7
);
    typedef enum {
        RED, GREEN, BLUE
    } Color;
    typedef struct {
        int x;
        int y;
    } Point;
    typedef Point VectorArray [3];
    typedef int IntMap [string];
    always_comb begin
        automatic Color my_color;
        automatic Point p1, p2;
        automatic VectorArray vectors;
        automatic IntMap sensor_readings;
        my_color = RED;
        if (sel == 2'b01) begin
            my_color = GREEN;
        end else if (sel == 2'b10) begin
            my_color = BLUE;
        end
        p1.x = data_in_7;
        p1.y = data_in_7 + 1;
        p2.x = p1.x * 2;
        p2.y = p1.y * 3;
        vectors[0] = p1;
        vectors[1] = p2;
        vectors[2].x = p1.x + p2.x;
        vectors[2].y = p1.y + p2.y;
        sensor_readings["temp_sensor_a"] = 25;
        sensor_readings["pressure_sensor_b"] = 100;
        result_7 = vectors[my_color].x + vectors[my_color].y;
        result_7 = result_7 + sensor_readings["temp_sensor_a"];
        result_7 = result_7 + my_color;
    end
endmodule
module AstNode_Module8 (
    input logic clk_8,
    output logic [31:0] output_val_8
);
    MyInterface if_inst (.clk(clk_8));
    inner_module inner_inst (
        .master_port(if_inst.MASTER),
        .slave_port(if_inst.SLAVE)
    );
    localparam MY_CONSTANT = 10;
    assign output_val_8 = (if_inst.MASTER.data + if_inst.SLAVE.data) + MY_CONSTANT;
endmodule
