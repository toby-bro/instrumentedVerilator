class MyPacket;
    rand bit [7:0] header;
    rand bit [15:0] payload;
    function new(bit [7:0] h, bit [15:0] p);
        this.header = h;
        this.payload = p;
    endfunction
    function bit [23:0] get_full_data();
        return {this.header, this.payload};
    endfunction
endclass
module ModuleSelectionsAndConcats (
    input logic [31:0] in_data_a,
    input logic [15:0] in_data_b,
    input logic [7:0] in_data_c,
    input logic [4:0] idx_a,
    input logic [2:0] idx_b,
    output logic [63:0] out_concat_full,
    output logic [15:0] out_part_select,
    output logic out_bit_select,
    output logic [3:0] out_dynamic_select,
    output logic [31:0] out_unpacked_element,
    output logic [7:0] out_packed_element
);
    logic [63:0] temp_concat;
    logic [31:0] temp_unpacked_array [0:1];
    logic [7:0] packed_array [3:0];
    assign temp_unpacked_array[0] = in_data_a;
    assign temp_unpacked_array[1] = {in_data_b, in_data_c, 8'hAA, 8'hBB};
    assign packed_array[0] = in_data_c;
    assign packed_array[1] = in_data_c + 1;
    assign packed_array[2] = in_data_c + 2;
    assign packed_array[3] = in_data_c + 3;
    assign temp_concat = {in_data_a, in_data_b, in_data_c, 8'hFF, 8'hEE, 8'hDD, 8'hCC};
    assign out_concat_full = temp_concat;
    assign out_part_select = in_data_a[23:8];
    assign out_bit_select = in_data_b[idx_b];
    assign out_dynamic_select = in_data_a[idx_a +: 4];
    assign out_unpacked_element = temp_unpacked_array[idx_b[0]];
    assign out_packed_element = packed_array[idx_b];
endmodule
module ModuleConditionalLogic (
    input logic [7:0] in_val_a,
    input logic [7:0] in_val_b,
    input logic [7:0] in_val_c,
    input logic cond_p,
    input logic cond_q,
    input logic cond_r,
    output logic [7:0] out_result_if,
    output logic [7:0] out_result_cond
);
    always_comb begin
        if (cond_p) begin
            if (cond_q) begin
                out_result_if = in_val_a + in_val_b;
            end else begin
                out_result_if = in_val_a - in_val_c;
            end
        end else begin
            if (cond_r) begin
                out_result_if = in_val_b * 2;
            end else begin
                out_result_if = in_val_c / 2;
            end
        end
    end
    assign out_result_cond = cond_p ?
                             (cond_q ? in_val_a : in_val_b) :
                             (cond_r ? in_val_c : (in_val_a + in_val_c));
endmodule
module ModuleConcurrency (
    input logic clk,
    input logic reset_n,
    input logic enable_op,
    input logic [7:0] in_data,
    output logic [15:0] out_val,
    output logic flag_out,
    output logic [7:0] out_internal_reg1_debug,
    output logic [15:0] out_fork_comb_val
);
    logic [7:0] internal_reg1;
    logic [7:0] internal_reg2;
    logic [7:0] internal_reg3;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            internal_reg1 <= 8'h0;
            internal_reg2 <= 8'h0;
            internal_reg3 <= 8'h0;
            out_val <= 16'h0;
            flag_out <= 1'b0;
        end else if (enable_op) begin
            fork : parallel_operations
                begin
                    internal_reg1 <= in_data + 1;
                    if (in_data > 10) begin
                        internal_reg1 <= internal_reg1 * 2;
                    end
                end
                begin
                    internal_reg2 <= in_data - 1;
                    internal_reg2 <= internal_reg2 | 8'hF0;
                    internal_reg3 <= internal_reg2 + 5;
                end
            join
            flag_out <= (internal_reg1 == internal_reg3);
            out_val <= {internal_reg1, internal_reg3};
        end else begin
            internal_reg1 <= internal_reg1;
            internal_reg2 <= internal_reg2;
            internal_reg3 <= internal_reg3;
            flag_out <= 1'b0;
            out_val <= 16'h0;
        end
    end
    always_comb begin : another_comb_block
        logic [7:0] temp_calc1, temp_calc2;
        temp_calc1 = in_data + in_data;
        temp_calc2 = in_data << 1;
        out_fork_comb_val = {temp_calc1, temp_calc2};
    end
    assign out_internal_reg1_debug = internal_reg1;
endmodule
module ModuleFunctionsAndTasks (
    input logic [7:0] in_val1,
    input logic [7:0] in_val2,
    input logic [7:0] in_val3,
    input logic [7:0] in_val4,
    output logic [7:0] func_result_out,
    output logic [7:0] task_result_out
);
    function automatic [7:0] calculate_sum (input [7:0] a, input [7:0] b);
        return a + b;
    endfunction
    task automatic process_values (input [7:0] val_in, output [7:0] val_out);
        val_out = val_in * 3;
        if (val_in > 50) begin
            val_out = val_out - 10;
        end
    endtask
    always_comb begin
        func_result_out = calculate_sum(in_val1, in_val2);
        func_result_out = calculate_sum(func_result_out, in_val3);
    end
    logic [7:0] temp_task_res;
    always_comb begin
        process_values(in_val4, temp_task_res);
        task_result_out = temp_task_res;
    end
endmodule
module ModuleGeneralLogic (
    input logic clk,
    input logic reset_n,
    input logic [7:0] data_in_a,
    input logic [7:0] data_in_b,
    input logic [7:0] data_in_c,
    input logic enable_proc,
    output logic [7:0] output_reg_a,
    output logic [7:0] output_reg_b,
    output logic [7:0] output_comb_c,
    output logic [7:0] output_loop_sum
);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            output_reg_a <= 8'h00;
            output_reg_b <= 8'h00;
        end else if (enable_proc) begin
            output_reg_a <= (data_in_a + data_in_b) & 8'hFF;
            output_reg_b <= (data_in_c | data_in_a) ^ data_in_b;
            if (data_in_a > data_in_b) begin
                output_reg_a <= output_reg_a + 1;
            end else begin
                output_reg_b <= output_reg_b - 1;
            end
        end
    end
    always_comb begin
        output_comb_c = (data_in_a == data_in_b) ? data_in_c : (data_in_a >> 1);
        output_comb_c = output_comb_c + (data_in_b << 2);
    end
    always_comb begin
        logic [7:0] sum = 8'h00;
        for (int i = 0; i < 4; i++) begin
            sum = sum + data_in_a[i*2 +: 2];
            if (sum > 8'hF0) begin
                sum = 8'hF0;
            end
        end
        output_loop_sum = sum;
    end
endmodule
module ModuleClasses (
    input logic clk,
    input logic reset_n,
    input logic create_packet,
    input logic [7:0] in_header,
    input logic [15:0] in_payload,
    output logic [23:0] out_packet_data,
    output logic is_packet_valid
);
    MyPacket pkt_h;
    logic [23:0] temp_data;
    always_ff @(posedge clk or negedge reset_n) begin
        MyPacket temp_new_pkt_handle;
        if (!reset_n) begin
            pkt_h <= null;
            out_packet_data <= 24'h0;
            is_packet_valid <= 1'b0;
        end else begin
            if (create_packet) begin
                temp_new_pkt_handle = new(in_header, in_payload);
                pkt_h <= temp_new_pkt_handle;
                is_packet_valid <= 1'b1;
            end else if (pkt_h != null) begin
                pkt_h <= pkt_h;
                is_packet_valid <= 1'b1;
            end else begin
                pkt_h <= null;
                is_packet_valid <= 1'b0;
            end
            if (pkt_h != null) begin
                temp_data <= pkt_h.get_full_data();
                out_packet_data <= temp_data;
                if (pkt_h.header == 8'hAA) begin
                    out_packet_data[7:0] <= pkt_h.payload[7:0];
                end
            end else begin
                out_packet_data <= 24'h0;
            end
        end
    end
endmodule
module ModuleProceduralTask (
    input logic clk_i,
    input logic reset_ni,
    input logic enable_i,
    input logic [7:0] data_in_i,
    output logic [7:0] data_out_o,
    output logic [7:0] internal_state_o
);
    logic [7:0] internal_data;
    task automatic my_processing_task(input bit enable, input [7:0] in_d, input [7:0] module_internal_data, output [7:0] out_d, output [7:0] task_state_snapshot);
        if (enable) begin
            out_d = in_d + 1;
            if (in_d > 50) begin
                out_d = out_d * 2;
            end
        end else begin
            out_d = in_d;
        end
        task_state_snapshot = module_internal_data;
    endtask
    always_ff @(posedge clk_i or negedge reset_ni) begin
        if (!reset_ni) begin
            internal_data <= 8'h0;
            data_out_o <= 8'h0;
            internal_state_o <= 8'h0;
        end else begin
            my_processing_task(enable_i, data_in_i, internal_data, data_out_o, internal_state_o);
            internal_data <= data_out_o;
        end
    end
endmodule
