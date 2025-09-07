import "DPI-C" function int sv_dpi_multiply(int a, int b);
import "DPI-C" function void sv_dpi_set_value(int val);
class MyClass;
    int data;
    function new(int init_data);
        this.data = init_data;
    endfunction
    function int multiply_by_factor(int factor);
        return data * factor;
    endfunction
endclass
module mod_array_concat_select (
    input logic [31:0] input_data,
    input logic [4:0] index,
    input logic [4:0] lsb_idx,
    output logic [63:0] output_concat,
    output logic [31:0] output_indexed,
    output logic [15:0] output_part
);
    logic [31:0] data_array [0:9];
    logic [31:0] temp_data;
    always_comb begin
        for (int i = 0; i < 10; i++) begin
            data_array[i] = input_data + i;
        end
        if (index < 10) begin
            output_indexed = data_array[index];
        end else begin
            output_indexed = '0;
        end
        if (lsb_idx < 17) begin
            output_part = data_array[0][lsb_idx +: 16];
        end else begin
            output_part = '0;
        end
        temp_data = input_data + 100;
        output_concat = {input_data, temp_data};
    end
endmodule
module mod_conditional_logic (
    input logic cond1,
    input logic cond2,
    input logic [7:0] val1,
    input logic [7:0] val2,
    output logic [7:0] out_if,
    output logic [7:0] out_cond
);
    always_comb begin
        if (cond1) begin
            out_if = val1 + 1;
        end else begin
            out_if = val2 - 1;
        end
    end
    assign out_cond = cond2 ? (val1 * 2) : (val2 / 2);
endmodule
module mod_fork_wait_example (
    input logic clk,
    input logic rst_n,
    input logic trigger_wait,
    input logic [7:0] data_in_fork,
    input logic [1:0] fork_idx,
    output logic [15:0] output_fork_sum,
    output logic [7:0] output_wait_val
);
    logic [7:0] local_val_proc1;
    logic [7:0] local_val_proc2;
    logic [7:0] wait_status_flag_reg;
    logic [15:0] output_fork_sum_reg;
    logic [7:0] output_wait_val_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            output_fork_sum_reg = '0;
            output_wait_val_reg = '0;
            wait_status_flag_reg = '0;
        end else begin
            output_fork_sum_reg = '0; 
            output_wait_val_reg = '0;
            wait_status_flag_reg = '0;
            fork
                begin
                    local_val_proc1 = data_in_fork + 1;
                    output_fork_sum_reg = output_fork_sum_reg + local_val_proc1;
                end
                begin
                    if (fork_idx == 2'b01) begin
                        local_val_proc2 = data_in_fork * 2;
                        output_fork_sum_reg = output_fork_sum_reg + local_val_proc2;
                    end
                end
                begin
                    output_wait_val_reg = data_in_fork + 5;
                    wait (trigger_wait);
                    output_wait_val_reg = output_wait_val_reg + 10;
                    wait_status_flag_reg = 1;
                end
            join_none
        end
    end
    assign output_fork_sum = output_fork_sum_reg;
    assign output_wait_val = output_wait_val_reg;
endmodule
module mod_dpi_class_active (
    input logic [31:0] dpi_input_val,
    input logic [7:0] class_factor,
    output logic [31:0] dpi_output_val,
    output logic [31:0] class_result
);
    always_comb begin
        MyClass my_instance;
        logic [31:0] local_dpi_res;
        local_dpi_res = sv_dpi_multiply(dpi_input_val, 5);
        sv_dpi_set_value(local_dpi_res);
        dpi_output_val = local_dpi_res;
        my_instance = new(dpi_input_val + 10);
        class_result = my_instance.multiply_by_factor(class_factor);
    end
endmodule
