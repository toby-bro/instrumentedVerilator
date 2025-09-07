module ModuleBasic (
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    logic [7:0] internal_var;
    localparam int MY_PARAM = 10; 
    integer counter_int; 
    logic [7:0] public_sig /* verilator public */ ; 
    always_comb begin
        internal_var = in_data + MY_PARAM; 
        public_sig = in_data + 1; 
        out_data = internal_var + public_sig; 
    end
    always_ff @(posedge in_data[0]) begin
        counter_int <= counter_int + 1; 
    end
endmodule
module ModuleWithClasses (
    input logic clk,
    input logic reset,
    output logic [3:0] class_result
);
    class MySimpleClass;
        rand int member_data; 
        function new();
            member_data = 0;
        endfunction
        function int get_data(int increment); 
            member_data = member_data + increment;
            return member_data;
        endfunction
    endclass
    MySimpleClass my_instance; 
    logic [3:0] temp_class_result;
    always_comb begin
        if (my_instance == null) begin
            my_instance = new();
        end
        temp_class_result = my_instance.get_data(1); 
        class_result = temp_class_result;
    end
endmodule
module ModuleWithConstraints (
    input logic enable_rand,
    output logic [7:0] out_val
);
    randc logic [7:0] randc_var; 
    rand logic [7:0] rand_var_a;
    rand logic [7:0] rand_var_b;
    constraint c_randc_illegal_solve_before {
        solve rand_var_a before randc_var; 
    }
    constraint c_rand_dist {
        rand_var_b dist { [1:5] :/ 20, [6:10] :/ 80 };
    }
    constraint c_soft_expr {
        soft (rand_var_a > 50);
    }
    always_comb begin
        if (enable_rand) begin
            void'(this.randomize()); 
            out_val = randc_var + rand_var_a + rand_var_b;
        end else begin
            out_val = 0;
        end
    end
endmodule
module ModuleInitialAutomaticAssert (
    input logic clk,
    input logic reset,
    input logic data_in,
    output logic data_out
);
    logic internal_sig;
    task automatic my_proc_task(input logic val_in); 
        logic task_local_var;
        initial automatic begin 
            task_local_var = val_in;
        end
        internal_sig = task_local_var;
    endtask
    sequence s_data_stable;
        @(posedge clk) (data_in == 1'b1) ##1 (data_in == 1'b1);
    endsequence
    assert property (@(posedge clk) reset |-> s_data_stable);
    always_comb begin
        my_proc_task(data_in);
        data_out = internal_sig;
    end
endmodule
module ModuleFunctionsTasksLet (
    input int a,
    input int b,
    output int sum_out,
    output int diff_out,
    output int let_result_out
);
    function int my_function(input int val1, input int val2); 
        return val1 + val2;
    endfunction
    task my_task(input int in1, input int in2, output int out_sum); 
        out_sum = in1 - in2;
    endtask
    import "DPI-C" function int dpi_calc_sub(input int op1, input int op2);
    let my_let_expr(x, y) = x * y + 1;
    logic [31:0] temp_sum;
    logic [31:0] temp_diff;
    logic [31:0] temp_let_result;
    logic [31:0] dpi_res;
    always_comb begin
        temp_sum = my_function(a, b); 
        my_task(a, b, temp_diff);     
        temp_let_result = my_let_expr(a, b); 
        dpi_res = dpi_calc_sub(a, b); 
        sum_out = temp_sum;
        diff_out = temp_diff;
        let_result_out = temp_let_result + dpi_res; 
    end
endmodule
module ModuleCasePragmas (
    input logic [1:0] selector,
    input logic task_enable,
    output logic [3:0] case_out
);
    /* verilator public_module */ 
    logic [3:0] internal_case_val;
    always_comb begin
        case (selector)
            2'b00: internal_case_val = 4'd1;
            2'b01: internal_case_val = 4'd2;
            2'b10: internal_case_val = 4'd3;
            default: internal_case_val = 4'd0; 
        endcase
        case_out = internal_case_val;
    end
    task my_pragma_task(input logic enable);
        /* verilator public_task */ 
        /* verilator hier_block */  
        if (enable) begin
        end
    endtask
    always_comb begin
        /* verilator coverage_block_off */ 
        if (task_enable) begin
            my_pragma_task(task_enable);
        end
    end
endmodule
module ModuleFileAndFormat (
    input int input_val,
    output int sformat_out_int
);
    integer file_desc; 
    int read_val;
    string sformat_str;
    string sscanf_str;
    int scanned_int;
    logic [7:0] scanned_byte;
    always_comb begin
        file_desc = 32'h1234_5678; 
        void'($fclose(file_desc)); 
        void'($ferror(file_desc)); 
        void'($feof(file_desc));   
        void'($fread(read_val, file_desc)); 
        sformat_str = $sformatf("Val: %0d (0x%h), Mod: %m, Lib: %l, Skip: %*d, String: %s",
                                 input_val, input_val, 1, "Hello String!");
        sformat_out_int = sformat_str.len(); 
        sscanf_str = "Number 123 Hex_Val 7B Char A";
        void'($sscanf(sscanf_str, "Number %d Hex_Val %h Char %c", scanned_int, scanned_byte));
        void'($fscanf(file_desc, "File_Data %d", scanned_int));
    end
endmodule
primitive My_UDP (
    output out_val,
    input in_a,
    input in_b
);
    table
        0   0   : 0;
        0   1   : 1;
        1   0   : 1;
        1   1   : 0;
    endtable
endprimitive
module ModuleUDP (
    input logic val_a,
    input logic val_b,
    output logic udp_result
);
    My_UDP my_udp_instance (udp_result, val_a, val_b); 
endmodule
module ModuleGenBlocks (
    input int select_gen_if,
    input logic [7:0] data_in_gen,
    output logic [7:0] data_out_gen
);
    genvar i;
    logic [7:0] temp_gen_data [2];
    generate for (i = 0; i < 2; i = i + 1) begin : gen_loop
        always_comb begin
            temp_gen_data[i] = data_in_gen[i];
        end
    end
    endgenerate
    generate if (select_gen_if == 1) begin : gen_if_block
        always_comb begin
            data_out_gen = temp_gen_data[0] + 1; 
        end
    end else begin : gen_else_block
        always_comb begin
            data_out_gen = temp_gen_data[1]; 
        end
    end
    endgenerate
endmodule
interface My_Interface (input logic clk, input logic reset);
    logic data;
    modport master (
        input clk,
        output data
    );
    modport slave (
        input clk,
        input data
    );
endinterface
module ModuleInterfaceModport (
    input logic clk_in,
    input logic reset_in,
    input logic master_data_in,
    output logic slave_data_out
);
    My_Interface my_if(.clk(clk_in), .reset(reset_in));
    assign my_if.master.data = master_data_in; 
    always_comb begin
        slave_data_out = my_if.slave.data; 
    end
endmodule
module SimpleSubModule (input in_s, output out_s);
    assign out_s = in_s;
endmodule
module ModuleInstantiations (
    input logic in_top,
    output logic out_top
);
    SimpleSubModule inst_0 (.in_s(in_top), .out_s(out_top)); 
endmodule
