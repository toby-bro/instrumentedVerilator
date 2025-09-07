module SAMPLED_LogicSignals (
    input logic i_clk,
    input logic i_reset_n,
    input logic i_data_in,
    output logic o_data_sampled_reg,
    output logic o_data_comb_sampled
);
    logic internal_signal_a;
    logic internal_signal_b;
    logic internal_signal_c;
    assign o_data_comb_sampled = SAMPLED(i_data_in) ^ SAMPLED(internal_signal_a);
    assign internal_signal_c = SAMPLED(internal_signal_a) & i_data_in;
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            o_data_sampled_reg <= 1'b0;
            internal_signal_a <= 1'b0;
            internal_signal_b <= 1'b0;
        end else begin
            o_data_sampled_reg <= SAMPLED(i_data_in); 
            internal_signal_a <= i_data_in;
            internal_signal_b <= SAMPLED(internal_signal_a); 
        end
    end
endmodule
module SAMPLED_VectorAndArray (
    input logic clk_i,
    input logic rst_ni,
    input logic [7:0] data_vec_i,
    input logic [3:0][2:0] data_array_i, 
    output logic [7:0] sampled_vec_o,
    output logic [2:0] sampled_array_elem_o
);
    logic [7:0] internal_vec_reg;
    logic [3:0][2:0] internal_array_reg;
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            internal_vec_reg <= 8'h00;
            internal_array_reg <= '0;
            sampled_vec_o <= 8'h00;
            sampled_array_elem_o <= '0;
        end else begin
            internal_vec_reg <= data_vec_i;
            internal_array_reg <= data_array_i;
            sampled_vec_o <= SAMPLED(internal_vec_reg);
            sampled_array_elem_o <= SAMPLED(internal_array_reg[2]);
            sampled_array_elem_o[0] <= SAMPLED(internal_vec_reg[0]);
            sampled_array_elem_o[2:1] <= SAMPLED(internal_vec_reg[7:6]);
        end
    end
endmodule
module SAMPLED_ClassAndStruct (
    input logic clk,
    input logic rst,
    input int    in_int,
    output int   out_sampled_int,
    output logic out_sampled_struct_field
);
    typedef struct packed {
        logic [7:0] field1;
        logic       field2;
    } my_struct_t;
    my_struct_t s_reg;
    my_struct_t s_comb;
    class MyClass;
        rand int value;
        logic [15:0] status;
        function new(int v, logic [15:0] s);
            value = v;
            status = s;
        endfunction
    endclass
    MyClass my_obj;
    int sampled_class_value;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            s_reg.field1 <= 8'h0;
            s_reg.field2 <= 1'b0;
            my_obj = new(0, 16'h0); 
            out_sampled_int <= 0;
            out_sampled_struct_field <= 1'b0;
            sampled_class_value <= 0;
        end else begin
            s_reg.field1 <= in_int[7:0];
            s_reg.field2 <= in_int[8];
            out_sampled_struct_field <= SAMPLED(s_reg.field2);
            out_sampled_int <= SAMPLED(in_int);
            my_obj = new(in_int + 1, s_reg.field1);
            sampled_class_value <= SAMPLED(my_obj.value);
        end
    end
    always_comb begin
        s_comb.field1 = in_int[7:0] + 1;
        s_comb.field2 = in_int[0];
        if (SAMPLED(s_comb.field1[0])) begin
            out_sampled_struct_field = 1'b1;
        end else begin
            out_sampled_struct_field = 1'b0;
        end
    end
endmodule
module SAMPLED_ComplexTypes (
    input logic clk,
    input logic rst_n,
    input int   value_in,
    input logic [7:0] arr_in [0:3], 
    output int  sampled_val_out,
    output logic [7:0] sampled_arr_elem_out,
    output logic sampled_enum_out
);
    enum { STATE_IDLE, STATE_RUNNING, STATE_DONE } current_state;
    enum { STATE_IDLE, STATE_RUNNING, STATE_DONE } next_state;
    logic [7:0] internal_unpacked_array [0:3];
    class MyComplexData;
        rand int    data_int;
        logic [3:0] data_logic_vec;
        function new(int i, logic [3:0] l);
            data_int = i;
            data_logic_vec = l;
        endfunction
    endclass
    MyComplexData complex_obj_reg;
    int sampled_complex_int;
    logic [3:0] sampled_complex_vec;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state <= STATE_IDLE;
            next_state <= STATE_IDLE;
            sampled_val_out <= 0;
            sampled_arr_elem_out <= 8'h00;
            sampled_enum_out <= 1'b0;
            for (int i=0; i<4; i++) internal_unpacked_array[i] <= 8'h00;
            complex_obj_reg = new(0, 4'b0); 
            sampled_complex_int <= 0;
            sampled_complex_vec <= 4'b0;
        end else begin
            current_state <= next_state;
            next_state <= (value_in > 10) ? STATE_RUNNING : STATE_IDLE;
            for (int i=0; i<4; i++) internal_unpacked_array[i] <= arr_in[i] + 1;
            sampled_enum_out <= SAMPLED(current_state) == STATE_RUNNING;
            sampled_arr_elem_out <= SAMPLED(internal_unpacked_array[2]);
            if (SAMPLED(value_in) > 50) begin
                sampled_val_out <= SAMPLED(value_in) - 10;
            end else begin
                sampled_val_out <= SAMPLED(value_in) + 10;
            end
            complex_obj_reg = new(value_in, arr_in[0][3:0]);
            sampled_complex_int <= SAMPLED(complex_obj_reg.data_int);
            sampled_complex_vec <= SAMPLED(complex_obj_reg.data_logic_vec);
        end
    end
endmodule
