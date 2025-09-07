module arithmetic_logic_complex (
    input logic [31:0] in_data_a,
    input logic [31:0] in_data_b,
    input logic [1:0] op_select,
    output logic [63:0] out_result_q
);
    localparam int unsigned LP_MAX_VAL = 32'hFFFF_FFFF;
    localparam real LP_PI_APPROX = 3.1415926535;
    localparam string LP_VERSION_STR = "SystemVerilog_Feature_Test_V1.0.0_Build_2024_Q2_RC_Final_Stable_Release_Candidate_For_Verilator_Coverage_Maximization_Attempt_Beta";
    localparam LP_FLAG_A = 1'b1;
    localparam LP_FLAG_B = 1'b0;
    logic [31:0] intermediate_mul;
    logic [31:0] intermediate_add;
    logic [31:0] intermediate_sub;
    logic [31:0] intermediate_div;
    logic [31:0] case_result_val;
    logic        flag_bit;
    logic [63:0] final_calc;
    int          loop_counter_i;
    int          loop_counter_j;
    int          loop_sum_k;
    always_comb begin : combinational_block
        intermediate_mul = in_data_a * in_data_b;
        intermediate_add = in_data_a + in_data_b;
        intermediate_sub = in_data_a - in_data_b;
        intermediate_div = (in_data_b != 0) ? (in_data_a / in_data_b) : 0; 
        flag_bit = (in_data_a > in_data_b) && (intermediate_add < LP_MAX_VAL) || LP_FLAG_A; 
        case (op_select)
            2'b00: case_result_val = intermediate_add;
            2'b01: case_result_val = intermediate_sub;
            2'b10: case_result_val = intermediate_mul;
            default: case_result_val = intermediate_div;
        endcase 
    end 
    always_ff @(posedge flag_bit) begin : sequential_block
        if (op_select == 2'b11) begin 
            out_result_q <= {intermediate_mul, intermediate_add} + case_result_val;
        end else if (op_select == 2'b10) begin
            out_result_q <= {intermediate_sub, intermediate_div} - (LP_MAX_VAL / 2);
        end else begin
            out_result_q <= LP_MAX_VAL * LP_MAX_VAL + in_data_a + in_data_b + LP_PI_APPROX; 
        end
    end
    task calculate_final_value (
        input longint val_in1,
        input longint val_in2,
        output longint val_out
    );
        longint temp_sum;
        temp_sum = val_in1 + val_in2;
        val_out = temp_sum * 2;
        for (loop_counter_i = 0; loop_counter_i < 10; loop_counter_i++) begin
            val_out += loop_counter_i;
        end
    endtask 
    function int get_scaled_value(input int original_val);
        return original_val * 3;
    endfunction 
    genvar gi;
    for (gi = 0; gi < 2; gi++) begin : gen_block
        logic [7:0] gen_interm;
        assign gen_interm = in_data_a[7:0] + gi;
        always_comb begin
            if (gen_interm > 10) begin
                final_calc[gi*8 +: 8] = gen_interm + 1;
            end else begin
                final_calc[gi*8 +: 8] = gen_interm;
            end
        end
    end
    always_comb begin : func_task_user
        longint task_out_var;
        int func_in_val = 15;
        calculate_final_value(in_data_a, in_data_b, task_out_var);
        final_calc[31:0] = task_out_var + get_scaled_value(func_in_val);
        loop_sum_k = 0;
        loop_counter_j = 0;
        while (loop_counter_j < 5) begin
            loop_sum_k += loop_counter_j;
            loop_counter_j++;
        end
        final_calc[63:32] = loop_sum_k; 
    end
    assign out_result_q = final_calc;
endmodule 
module type_declaration_test (
    input logic [7:0] input_byte,
    output logic [15:0] output_word
);
    typedef enum logic [1:0] {
        STATE_IDLE,
        STATE_ACTIVE,
        STATE_PAUSED,
        STATE_DONE
    } my_state_e;
    my_state_e current_state;
    my_state_e next_state;
    typedef struct packed {
        logic [3:0] id;
        logic [7:0] value;
    } my_packed_struct_t;
    my_packed_struct_t p_data;
    typedef struct {
        string      name_str;
        int         count;
        real        ratio;
        my_packed_struct_t config;
    } my_unpacked_struct_t;
    my_unpacked_struct_t u_data;
    typedef union packed {
        logic [31:0]   all_bits;
        struct packed {
            logic [15:0] low_half;
            logic [15:0] high_half;
        } halves;
        logic [7:0]    bytes [4]; 
    } my_union_t;
    my_union_t u_inst;
    int my_2d_array[2][3];
    my_unpacked_struct_t assoc_map_by_name [string];
    int int_queue[$];
    always_comb begin : type_usage_block
        current_state = STATE_IDLE;
        case (input_byte[1:0])
            2'b00: next_state = STATE_IDLE;
            2'b01: next_state = STATE_ACTIVE;
            2'b10: next_state = STATE_PAUSED;
            default: next_state = STATE_DONE;
        endcase
        p_data.id = input_byte[7:4];
        p_data.value = input_byte;
        u_data.name_str = "Example \"Name\" with \\slashes\\ and newline\\nchars for Verilator output"; 
        u_data.count = input_byte * 10;
        u_data.ratio = 1.0 / (input_byte + 1);
        u_data.config = p_data; 
        u_inst.all_bits = {16'hAAAA, input_byte, {8'hFF, 8'h00}}; 
        output_word = u_inst.halves.low_half + u_inst.bytes[0];
        my_2d_array[0][0] = 100;
        my_2d_array[1][2] = input_byte;
        assoc_map_by_name["entry_one"] = u_data;
        if (!int_queue.empty()) int_queue.delete();
        int_queue.push_back(input_byte);
        int_queue.push_front(input_byte + 1);
        if (current_state == STATE_DONE && next_state == STATE_IDLE) begin
            output_word = output_word + 1;
        end else begin
            output_word = output_word * 2;
        end
    end
endmodule
package my_complex_package;
    export my_complex_package::*; 
    import my_complex_package::MyClassInPackage; 
    parameter PKG_DATA_WIDTH = 64;
    parameter PKG_DEPTH      = 8;
    typedef logic [PKG_DATA_WIDTH-1:0] data_array_t [PKG_DEPTH];
    typedef struct {
        int         addr;
        logic       enable;
        bit [3:0]   priority;
        data_array_t payload; 
    } packet_info_t;
    class MyClassInPackage; 
        int m_id;
        string m_name;
        packet_info_t m_packet;
        function new(int id_val, string name_val); 
            this.m_id = id_val;
            this.m_name = name_val;
            m_packet.addr = 0;
            m_packet.enable = 1'b0;
            m_packet.priority = 4'hF;
            foreach (m_packet.payload[idx]) m_packet.payload[idx] = '0; 
        endfunction
        function automatic int get_id(); 
            return m_id;
        endfunction
        task set_payload(input data_array_t new_payload);
            this.m_packet.payload = new_payload;
        endtask
        function void print_info(input string prefix);
            string info_string = {prefix, ": ID=", $sformatf("%0d", m_id), ", Name=", m_name, ", Addr=", $sformatf("%0d", m_packet.addr)};
        endfunction
    endclass 
    function automatic int factorial(input int n);
        if (n <= 1) return 1;
        return n * factorial(n - 1);
    endfunction
endpackage 
interface my_simple_interface (input logic clk); 
    logic enable;
    logic [7:0] data_in;
    logic [15:0] result_out;
    modport master (output enable, output data_in, input result_out);
    modport slave (input enable, input data_in, output result_out);
endinterface 
module class_interface_package_integration ( 
    input logic clk,
    input logic rst_n,
    input logic [7:0] global_data_in,
    output logic [15:0] global_result_out
);
    import my_complex_package::*;
    my_simple_interface i_if (.clk(clk));
    my_complex_package::MyClassInPackage class_inst_a;
    my_complex_package::MyClassInPackage class_inst_b;
    my_complex_package::MyClassInPackage class_inst_c; 
    always_ff @(posedge clk or negedge rst_n) begin : class_usage_block
        if (!rst_n) begin
            class_inst_a = new(10, "First Instance: \"ID_10\" \\Path\\/Segments\\nfor \\Protector\\");
            class_inst_b = new(20, "Second Instance: `Complex` Name for \"Identifier Testing\"");
            class_inst_c = new(30, "Third Instance: With \"Another\" Long \\Name\\ for Extensive Testing");
            i_if.enable <= 1'b0;
            i_if.data_in <= 8'h00;
            global_result_out <= 16'h0000;
        end else begin
            i_if.enable <= 1'b1;
            i_if.data_in <= global_data_in;
            global_result_out <= i_if.result_out + class_inst_a.get_id();
            data_array_t temp_payload;
            for (int k = 0; k < PKG_DEPTH; k++) begin
                temp_payload[k] = k + global_data_in;
            end
            class_inst_a.set_payload(temp_payload);
            class_inst_a.print_info("DebugPrint_For_InstanceA"); 
        end
    end
    assign i_if.enable = 1'b1; 
    assign i_if.data_in = global_data_in + 1; 
    assign global_result_out = i_if.result_out + factorial(5); 
endmodule
module port_and_expression_diversity (
    input signed int [63:0] input_large_vector,
    input real              input_real_val,
    output signed longint   output_final_sum
);
    byte my_byte_var;
    shortint my_short_int_var;
    int my_int_var;
    longint my_long_int_var;
    integer my_integer_var;
    real my_real_var;
    time my_time_var; 
    logic [7:0] packed_array [4]; 
    bit unpacked_bit_array [5][3]; 
    always_comb begin : expression_block
        my_byte_var = input_large_vector[7:0];
        my_short_int_var = input_large_vector[15:8];
        my_int_var = input_large_vector[31:0];
        my_long_int_var = input_large_vector;
        my_integer_var = $floor(input_real_val * 100);
        my_real_var = input_real_val * 2.5 + my_long_int_var / 100.0;
        my_time_var = $time; 
        output_final_sum = (my_long_int_var + (my_int_var >>> 2) * my_short_int_var) - ($signed(my_byte_var) ** 3) + $floor(my_real_var / 0.75); 
        packed_array[0] = input_large_vector[63:56];
        packed_array[1] = input_large_vector[55:48];
        packed_array[2] = input_large_vector[47:40];
        packed_array[3] = input_large_vector[39:32];
        unpacked_bit_array[0][0] = 1'b1;
        unpacked_bit_array[4][2] = input_large_vector[0];
        output_final_sum = output_final_sum + (input_large_vector[0] ? my_byte_var * my_short_int_var + my_int_var / 2 - my_long_int_var % 10 + my_integer_var ** 2 : my_real_var * 100.0 - my_time_var / 10.0 + input_large_vector[63] + input_large_vector[62] + input_large_vector[61] + input_large_vector[60] + input_large_vector[59] + input_large_vector[58] + input_large_vector[57] + input_large_vector[56] + input_large_vector[55] + input_large_vector[54] + input_large_vector[53] + input_large_vector[52] + input_large_vector[51] + input_large_vector[50] + input_large_vector[49] + input_large_vector[48] + input_large_vector[47] + input_large_vector[46] + input_large_vector[45] + input_large_vector[44] + my_byte_var + my_short_int_var + my_int_var + my_long_int_var + my_integer_var + my_real_var);
    end
    always_latch begin : latch_block
        if (input_large_vector[0]) begin
            my_byte_var <= input_large_vector[7:0] + 1;
        end
    end
endmodule
