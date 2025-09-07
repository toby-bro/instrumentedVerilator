module Module_Linting_Errors (
    input logic in_data,
    output logic out_flag
);
    assign undeclared_wire = in_data;
    logic [7:0] my_reg;
    logic [7:0] my_wire;
    assign my_wire = 8'hAA;
    assign my_wire = 8'hBB;
    always_comb begin
        if (in_data) begin
            my_reg = 8'd10;
        end
    end
    logic clk, reset_n;
    logic ff_out_q;
    input logic ff_in_d;
    /* verilator lint_off BLKANDDFF */
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            ff_out_q = 1'b0; 
        else
            ff_out_q = ff_in_d;
    end
    /* verilator lint_on BLKANDDFF */
    logic unused_signal;
    assign unused_signal = 1'b1;
    /* verilator lint_off ASSIGNDLY */
    assign #1 out_flag = my_reg[0]; 
    /* verilator lint_on ASSIGNDLY */
    assign out_flag = (8'hFF > -1);
endmodule
module Module_Width_Type_Errors (
    input logic [3:0] in_val,
    output logic [7:0] out_val
);
    logic [2:0] smaller_reg;
    logic [5:0] larger_wire;
    assign smaller_reg = in_val; 
    assign larger_wire = in_val; 
    int signed_var;
    logic [3:0] unsigned_var;
    assign signed_var = unsigned_var; 
    bit [7:0] my_byte_val;
    bit [3:0] my_nybble_val;
    assign my_nybble_val = my_byte_val; 
    assign out_val = {larger_wire, smaller_reg, my_nybble_val[0]}; 
endmodule
module Module_Procedural_Errors (
    input logic [1:0] sel_in,
    output logic [3:0] result_out
);
    logic [3:0] case_reg;
    logic [1:0] selector;
    always_comb begin
        casez (sel_in)
            2'b0?: case_reg = 4'h1;
            2'b10: case_reg = 4'h2;
            default: case_reg = 4'h0;
        endcase
    end
    always_comb begin
        static int count; 
        if (sel_in == 2'b00) begin
            result_out = case_reg;
        end else if (sel_in == 2'b01) begin
            result_out = sel_in + 1;
        end else begin
            result_out = count[3:0]; 
            count++; 
        end
    end
    logic [7:0] temp_val;
    always @(*) begin 
        temp_val = 8'd5;
        temp_val <= 8'd10; 
    end
    logic [3:0] output_latch;
    assign selector = sel_in;
    always_comb begin
        case (selector)
            2'b00: output_latch = 4'hA;
            2'b01: output_latch = 4'hB;
        endcase
    end
endmodule
module Module_Function_Task_Errors (
    input logic [7:0] data_in_ft,
    output logic [7:0] data_out_ft
);
    function automatic [7:0] my_func_noassign;
        input [7:0] a;
    endfunction
    task automatic my_task_var_ports;
        input logic [7:0] i_val;
        output var logic [7:0] o_val; 
        o_val = i_val + 1;
    endtask
    function automatic logic [7:0] add_one_func;
        input [7:0] val;
        add_one_func = val + 1;
    endfunction
    logic [7:0] temp_result_func_call;
    logic [7:0] temp_result_task_call;
    always_comb begin
        temp_result_func_call = add_one_func(data_in_ft, 1'b1);
    end
    always_comb begin
        my_task_var_ports(data_in_ft, temp_result_task_call);
    end
    function automatic int factorial;
        input int n;
        if (n <= 1)
            factorial = 1;
        else
            factorial = n * factorial(n - 1); 
    endfunction
    assign data_out_ft = temp_result_func_call + temp_result_task_call + factorial(data_in_ft[3:0] < 8 ? data_in_ft[3:0] : 8'h8);
endmodule
module Module_Parameter_Generic_Errors #(
    parameter int P_UNUSED = 10, 
    parameter int P_MAX_VAL = 20,
    parameter logic [3:0] P_BAD_TYPE = 5
) (
    input logic [7:0] value_in,
    output logic [7:0] value_out
);
    assign value_out = value_in + undefined_variable;
    genvar i;
    generate
        for (i = 0; i < P_MAX_VAL; i++) begin : gen_loop
            localparam JUNK = P_BAD_TYPE + i; 
        end
    endgenerate
    localparam int CONFLICT_PARAM = 1;
    localparam int CONFLICT_PARAM = 2; 
    assign value_out = value_in + P_MAX_VAL;
endmodule
module Module_System_Task_Errors (
    input logic control_error,
    input logic control_warning,
    output logic dummy_out
);
    logic [7:0] data_value = 8'h0;
    always_comb begin
        if (control_error) begin
            $error("SystemVerilog $error task triggered. Data value: %h", data_value);
        end
    end
    always_comb begin
        if (control_warning) begin
            $warning("SystemVerilog $warning task triggered. Data value: %d", data_value);
        end
    end
    always_comb begin
        if (data_value == 8'h0) begin 
            $fatal(1, "SystemVerilog $fatal task triggered. Data was zero.");
        end
    end
    assign dummy_out = control_error | control_warning;
endmodule
module Module_Hard_Error_Limit_Test (
    input logic [7:0] val_a,
    input logic [7:0] val_b,
    output logic [7:0] result_c
);
    logic [3:0] small_val;
    logic [15:0] big_val;
    logic [7:0] other_val;
    assign small_val = val_a; 
    assign big_val = undeclared_signal_for_error;
    assign other_val = val_a + val_b;
    assign other_val = val_a - val_b;
    logic unused_wire_error;
    assign unused_wire_error = 1'b0;
    logic [1:0] sel_input;
    logic [7:0] latch_output;
    assign sel_input = val_a[1:0];
    always_comb begin
        case (sel_input)
            2'b00: latch_output = val_a;
            2'b01: latch_output = val_b;
        endcase
    end
    logic [7:0] mix_assign_val;
    always_comb begin
        mix_assign_val = val_a;
        mix_assign_val <= val_b;
    end
    localparam int P_REDEF_TEST = 10;
    localparam int P_REDEF_TEST = 20; 
    assign result_c = val_a + (val_b + ; 
    assign result_c = small_val[3:0] + big_val[7:0] + other_val[7:0] + latch_output[7:0] + mix_assign_val[7:0];
endmodule
