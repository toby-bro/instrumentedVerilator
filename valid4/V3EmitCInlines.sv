module ClassInstantiationModule #(parameter DATA_WIDTH = 8) (
    input logic                 clk,
    input logic                 rst_n,
    input logic [DATA_WIDTH-1:0] in_data,
    output logic [DATA_WIDTH-1:0] out_data
);
    class MySimpleClass;
        rand int my_int_var;
        int my_other_var;
        function new(int init_val);
            my_int_var = init_val;
            my_other_var = init_val * 2;
        endfunction
    endclass
    MySimpleClass instance_a;
    MySimpleClass instance_b;
    initial begin
        instance_a = new MySimpleClass(10);
        instance_b = new MySimpleClass(20);
    end
    logic [DATA_WIDTH-1:0] reg_data_q;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            reg_data_q <= '0;
        end else begin
            reg_data_q <= in_data;
        end
    end
    always_comb begin
        if (instance_a != null && instance_b != null) begin
            out_data = reg_data_q + instance_a.my_int_var + instance_b.my_other_var;
        end else begin
            out_data = reg_data_q;
        end
    end
endmodule
module RandomDistModule (
    input logic                 clk,
    input logic                 rst_n,
    input logic                 trigger,
    output logic [7:0]          rand_val_out
);
    class RandomGenerator;
        rand byte rand_byte_var;
        rand int unsigned rand_uint_var;
        rand shortint rand_short_var;
        constraint byte_dist_con {
            rand_byte_var dist {0:=20, 1:=30, [10:20]:=50};
        }
        constraint uint_dist_con {
            rand_uint_var dist {100 := 10, 200 := 20, 300 := 30, [400:500] := 40};
        }
        constraint short_value_con {
            rand_short_var inside {[-5:5], 10, 20};
        }
        function new();
        endfunction
    endclass
    RandomGenerator rand_gen_instance;
    logic [7:0] local_rand_byte_val;
    initial begin
        rand_gen_instance = new RandomGenerator();
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            local_rand_byte_val <= '0;
        } else begin
            if (trigger && rand_gen_instance != null) begin
                void'(rand_gen_instance.randomize());
                local_rand_byte_val <= rand_gen_instance.rand_byte_var;
            end
        end
    end
    always_comb begin
        rand_val_out = local_rand_byte_val;
    end
endmodule
module AdvancedLogicModule (
    input logic [3:0]           select_in,
    input logic [7:0]           data_in_a,
    input logic [7:0]           data_in_b,
    output logic [7:0]          result_out
);
    typedef enum {ADD, SUB, MUL, DIV} op_t;
    op_t current_op;
    function automatic logic [7:0] calculate_sum(logic [7:0] a, logic [7:0] b);
        return a + b;
    endfunction
    task automatic update_result(input logic [7:0] val_a, input logic [7:0] val_b, output logic [7:0] res);
        res = val_a ^ val_b;
    endtask
    logic [7:0] temp_res;
    always_comb begin
        unique case (select_in)
            4'b0000: current_op = ADD;
            4'b0001: current_op = SUB;
            4'b0010: current_op = MUL;
            4'b0011: current_op = DIV;
            default: current_op = ADD;
        endcase
        priority if (current_op == ADD) begin
            result_out = calculate_sum(data_in_a, data_in_b);
        end else if (current_op == SUB) begin
            result_out = data_in_a - data_in_b;
        end else if (current_op == MUL) begin
            result_out = data_in_a * data_in_b;
        end else if (current_op == DIV) begin
            if (data_in_b != 0) begin
                result_out = data_in_a / data_in_b;
            end else begin
                result_out = '0;
                assert (! (data_in_b == 0)) else $error("Division by zero detected!");
            end
        end else begin
            result_out = '0;
        end
        update_result(data_in_a, data_in_b, temp_res);
        for (int i = 0; i < 4; i++) begin
            temp_res[i] = temp_res[i] ^ data_in_a[i+4];
        end
    end
    always_comb begin
        assert (data_in_a >= 0) else $error("Data_in_a should be non-negative");
    end
endmodule
module ComplexTypeModule (
    input logic                 data_valid,
    input logic [7:0]           data_payload,
    output logic [15:0]         processed_data
);
    union packed {
        logic [15:0] byte_access;
        logic [15:0] word_access;
    } my_union;
    typedef struct packed {
        logic [3:0] header;
        logic [7:0] payload;
    } packet_t;
    packet_t current_packet;
    logic [7:0] data_array [10];
    int associative_map [string];
    int int_queue [$];
    always_comb begin
        my_union.byte_access = {8'b0, data_payload};
        current_packet.header = data_valid ? 4'hF : 4'h0;
        current_packet.payload = data_payload;
        processed_data = {my_union.word_access[7:0], current_packet.payload};
        data_array[0] = data_payload;
        associative_map["key1"] = 10;
        if (associative_map.exists("key1")) begin
            associative_map["key2"] = associative_map["key1"] + 1;
        end
        int_queue.push_back(data_payload);
        if (int_queue.size() > 0) begin
            processed_data = processed_data + int_queue.pop_front();
        end
        int_queue.delete();
    end
endmodule
