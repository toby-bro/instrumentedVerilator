class MyConstrainedClass #(parameter CLASS_P = 10);
    randc int r_val;
    int m_data;
    localparam int LOCAL_P = 5;
    constraint c_solve_before {
        r_val inside {[1:100]};
    }
    constraint c_dist {
        m_data dist {10 := 40, 20 := 60};
    }
    constraint c_soft {
        soft m_data == CLASS_P + LOCAL_P;
    }
    function new();
        m_data = 0;
    endfunction
    function automatic int calculate(int in_arg);
        int local_func_var = in_arg + LOCAL_P;
        r_val = r_val + 1;
        return m_data + local_func_var;
    endfunction
    task automatic update_data(input int new_val);
        m_data = new_val;
        void'(this.randomize()); 
    endtask
    function void finalize();
    endfunction
    function automatic int get_internal_val();
        return m_data;
    endfunction
endclass
module ClassConstraintRandcGen (
    input int in_val,
    input bit clk,
    output int out_sum,
    output logic [7:0] data_out
);
    MyConstrainedClass c_inst;
    int temp_sum;
    logic [7:0] temp_data;
    always_ff @(posedge clk) begin
        if (c_inst == null) begin
            c_inst = new(); 
        end
        c_inst.update_data(in_val);
        temp_sum = c_inst.calculate(in_val);
        temp_data = c_inst.r_val[7:0]; 
    end
    assign out_sum = temp_sum;
    assign data_out = temp_data;
endmodule
(* hier_block *) 
module GenBlocksAndPragmas (
    input int gen_idx_in,
    input bit [1:0] sel_in,
    output int out_calc,
    output int out_cond
);
    genvar i;
    int internal_val_calc = 0;
    int internal_val_cond = 0;
    (* public task *) 
    function automatic int gen_func (input int val, input int factor);
        return val * factor;
    endfunction
    generate
        for (i = 0; i < 4; i = i + 1) begin : gen_loop 
            always_comb begin
                if (gen_idx_in == i) begin
                    internal_val_calc = gen_func(gen_idx_in, i); 
                end
            end
        end
    endgenerate
    generate
        if (sel_in == 2'b01) begin : gen_if_block 
            logic [3:0] temp_add;
            assign temp_add = gen_idx_in + 5;
            always_comb begin
                internal_val_cond = temp_add;
            end
        end else if (sel_in == 2'b10) begin : gen_else_if_block 
            int temp_mult;
            assign temp_mult = gen_idx_in * 2;
            always_comb begin
                internal_val_cond = temp_mult;
            end
        end else begin : gen_else_block 
            always_comb begin
                internal_val_cond = gen_idx_in;
            end
        end
    endgenerate
    assign out_calc = internal_val_calc;
    assign out_cond = internal_val_cond;
    (* coverage_block_off *) 
    always_comb begin : no_coverage_block
        logic [7:0] dummy_logic = 8'hFF;
        dummy_logic = dummy_logic + 1; 
    end
endmodule
module SystemTasksFormats (
    input int display_val,
    input string format_str_in,
    output int scan_out_int,
    output string sformat_out_str
);
    integer file_handle;
    int sscanf_temp_int;
    string sscanf_temp_str;
    string sformat_temp_str;
    always_comb begin
        file_handle = 0;
        sscanf_temp_int = 0;
        sscanf_temp_str = "";
        sformat_temp_str = "";
        sformat_temp_str = $sformatf("Decimal: %0d, Hex: %h, Binary: %b", display_val, display_val, display_val);
        sformat_temp_str = $sformatf("String: %s", format_str_in);
        sformat_temp_str = $sformatf("Module: %m, Path: %l");
        sformat_temp_str = $sformatf("Percent symbol: %%");
        sformat_temp_str = $sformatf("Padded: %4d, Prec: %.2f", display_val, display_val);
        sformat_temp_str = $sformatf("Hello, world!");
        void'($sscanf("12345 abc", "%d %s", sscanf_temp_int, sscanf_temp_str));
        scan_out_int = sscanf_temp_int;
        sformat_out_str = sscanf_temp_str;
        case (display_val)
            10: begin
                int temp_case = 1;
            end
            20: begin
                int temp_case = 2;
            end
            default: begin 
                int temp_case = 3;
            end
        endcase
    end
endmodule
interface simple_if (input bit clk);
    logic [7:0] data;
    logic valid;
    modport master ( 
        output data,
        output valid,
        input clk
    );
    modport slave ( 
        input data,
        input valid,
        input clk
    );
endinterface
module InterfaceModport (
    input int in_data_i,
    input bit clock_i,
    output int out_data_o,
    output bit valid_o
);
    simple_if s_if_inst (clock_i);
    class InterfaceUser;
        simple_if.slave if_slave_port; 
        function new(simple_if.slave port);
            if_slave_port = port;
        endfunction
        function int get_data();
            if (if_slave_port.valid)
                return if_slave_port.data;
            else
                return 0;
        endfunction
    endclass
    InterfaceUser user_inst;
    always_comb begin
        s_if_inst.master.data = in_data_i[7:0];
        s_if_inst.master.valid = 1'b1;
        if (user_inst == null) begin
            user_inst = new(s_if_inst.slave); 
        end
        out_data_o = user_inst.get_data();
        valid_o = s_if_inst.slave.valid;
    end
endmodule
primitive TwoOutputUdp (output Y1, Y2, input A, B);
    table
      0 0 : 0 1;
      0 1 : 1 0;
      1 0 : 1 0;
      1 1 : 0 1;
    endtable
endprimitive
primitive SingleOutputUdp (output Y, input A, B);
    table
      0 0 : 0;
      0 1 : 1;
      1 0 : 1;
      1 1 : 0;
    endtable
endprimitive
module UdpModuleTest (
    input bit i1, i2, i3,
    output bit o1, o2
);
    bit temp_single_o;
    SingleOutputUdp inst_single (temp_single_o, i1, i2);
    assign o1 = temp_single_o;
    bit temp_y1, temp_y2;
    TwoOutputUdp inst_two (temp_y1, temp_y2, i1, i3);
    assign o2 = temp_y1; 
endmodule
module LetStatementTests (
    input int val_in,
    output int result_out
);
    let add_five(x) = x + 5;
    let multiply_by_two(y) = y * 2;
    int temp_res1;
    int temp_res2;
    always_comb begin
        temp_res1 = add_five(val_in);
        temp_res2 = multiply_by_two(temp_res1);
        result_out = temp_res2;
    end
endmodule
package dpi_pkg;
    import "DPI-C" function void imported_dpi_func(input int val); 
    export "DPI-C" function void exported_dpi_func(input int val); 
endpackage
module DpiTestModule (
    input int in_val,
    output int out_val
);
    always_comb begin
        dpi_pkg::imported_dpi_func(in_val);
        dpi_pkg::exported_dpi_func(in_val); 
        out_val = in_val * 2;
    end
endmodule
