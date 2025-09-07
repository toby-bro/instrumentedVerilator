module BasicIsolationTest (
    input logic clk,
    input logic rst_n,
    input logic [7:0] in_data,
    input logic in_sel,
    output logic [7:0] out_isolated,
    output logic [7:0] out_other
);
    reg [7:0] /*verilator_isolate_assignments*/ isolated_internal_reg;
    reg [7:0] other_internal_reg;
    reg       some_flag_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            isolated_internal_reg <= '0;
            other_internal_reg <= '0;
            some_flag_reg <= '0;
        end else begin
            if (in_sel) begin
                isolated_internal_reg <= in_data + 1;
                other_internal_reg <= in_data - 1;
                some_flag_reg <= 1'b1;
            end else begin
                isolated_internal_reg <= in_data * 2;
                other_internal_reg <= in_data / 2;
                some_flag_reg <= 1'b0;
            end
            case (some_flag_reg)
                1'b1: begin
                    isolated_internal_reg <= isolated_internal_reg + 10;
                    other_internal_reg <= other_internal_reg + 1;
                end
                1'b0: begin
                    other_internal_reg <= other_internal_reg + 20;
                    isolated_internal_reg <= isolated_internal_reg + 2;
                end
            endcase
        end
    end
    assign out_isolated = isolated_internal_reg;
    assign out_other    = other_internal_reg;
endmodule
module IsolatedWithFunctions (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic [7:0] in_c,
    output logic [7:0] out_sum_func,
    output logic [7:0] out_mult_func
);
    logic [7:0] /*verilator_isolate_assignments*/ isolated_sum_var;
    logic [7:0] other_mult_var;
    function automatic logic [7:0] calculate_sum(logic [7:0] op1, op2, op3);
        return op1 + op2 + op3;
    endfunction
    function automatic logic [7:0] calculate_product(logic [7:0] op1, op2);
        return op1 * op2;
    endfunction
    always_comb begin
        isolated_sum_var = calculate_sum(in_a, in_b, in_c);
        other_mult_var   = calculate_product(in_a, in_b);
        if (calculate_sum(in_a, in_b, in_c) > 100) begin
            isolated_sum_var = calculate_sum(isolated_sum_var, 1, 0);
            other_mult_var   = calculate_product(other_mult_var, 3);
        end else begin
            isolated_sum_var = calculate_sum(isolated_sum_var, 2, 0);
            other_mult_var   = calculate_product(other_mult_var, 4);
        end
        isolated_sum_var = calculate_sum(isolated_sum_var, other_mult_var[0], 0);
    end
    assign out_sum_func = isolated_sum_var;
    assign out_mult_func = other_mult_var;
endmodule
module MultipleIsolatedVariables (
    input logic [7:0] data_in,
    input logic       sel_mode,
    output logic [7:0] out_val1,
    output logic [7:0] out_val2,
    output logic [7:0] out_val3
);
    logic [7:0] /*verilator_isolate_assignments*/ isolated_var1;
    logic [7:0] /*verilator_isolate_assignments*/ isolated_var2;
    logic [7:0] non_isolated_var;
    always_comb begin
        if (sel_mode) begin
            isolated_var1 = data_in + 5;
            isolated_var2 = data_in - 5;
            non_isolated_var = data_in * 2;
        end else begin
            isolated_var1 = data_in + 10;
            isolated_var2 = data_in - 10;
            non_isolated_var = data_in / 2;
        end
        isolated_var1 = isolated_var1 + non_isolated_var;
        isolated_var2 = isolated_var2 ^ non_isolated_var;
        case (data_in[1:0])
            2'b00: isolated_var1 = isolated_var1 + 1;
            2'b01: isolated_var2 = isolated_var2 + 1;
            2'b10: non_isolated_var = non_isolated_var + 1;
            default: begin
                isolated_var1 = isolated_var1 + 100;
                isolated_var2 = isolated_var2 + 200;
                non_isolated_var = non_isolated_var + 300;
            end
        endcase
    end
    assign out_val1 = isolated_var1;
    assign out_val2 = isolated_var2;
    assign out_val3 = non_isolated_var;
endmodule
module IsolationWithClassInstance (
    input logic [7:0] in_val,
    input logic in_trigger,
    output logic [7:0] out_processed_val,
    output logic [7:0] out_class_data
);
    class DataPacket;
        int m_data;
        function new(int init_data);
            this.m_data = init_data;
        endfunction
        function int get_data();
            return m_data;
        endfunction
        function void set_data(int new_data);
            this.m_data = new_data;
        endfunction
    endclass
    logic [7:0] /*verilator_isolate_assignments*/ isolated_result;
    logic [7:0] temp_data;
    logic [7:0] internal_class_data; 
    DataPacket my_packet;
    always_comb begin
        if (my_packet == null) begin
            my_packet = new(in_val);
        end else if (in_trigger) begin
            my_packet.set_data(my_packet.get_data() + in_val);
        end
        temp_data = my_packet.get_data() + 10;
        isolated_result = temp_data;
        if (in_val > 50) begin
            isolated_result = isolated_result + my_packet.get_data();
        end else begin
            isolated_result = isolated_result - my_packet.get_data();
        end
        internal_class_data = my_packet.get_data(); 
    end
    assign out_processed_val = isolated_result;
    assign out_class_data = internal_class_data; 
endmodule
