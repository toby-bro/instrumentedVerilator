module ClassConstraintModule (
    input bit clk_i,
    input bit reset_n_i,
    input logic [7:0] data_in_i,
    output logic [7:0] data_out_o
);
    class MyClass;
        randc int my_randc_var;
        rand int my_rand_var;
        int member_var;
        constraint c_randc_before {
            solve my_rand_var before my_randc_var;
            my_randc_var inside {[0:100]};
        }
        constraint c_dist {
            my_rand_var dist {10 := 1, 20 := 2, [30:40] := 5};
        }
        constraint c_soft_expr {
            soft my_rand_var < 50;
        }
        function void init_member_var(int val);
            member_var = val;
        endfunction
        extern function int generate_and_get();
    endclass
    function int MyClass::generate_and_get();
        if (!randomize(my_randc_var, my_rand_var)) begin
        end
        return my_randc_var + my_rand_var + member_var;
    endfunction
    MyClass my_instance;
    initial begin automatic
        int auto_dummy_var = 0;
        auto_dummy_var++;
    end
    initial begin
        int some_local_init_val = 1;
        my_instance = new();
        my_instance.init_member_var(some_local_init_val);
    end
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            data_out_o <= '0;
        end else begin
            if (my_instance != null) begin
                my_instance.my_rand_var = data_in_i;
                data_out_o <= my_instance.generate_and_get();
            end else begin
                data_out_o <= '0;
            end
        end
    end
endmodule
(* verilator_hier_block *)
(* verilator_public_module *)
module GenerateAndVarRefModule (
    input bit enable_i,
    input logic [3:0] select_i,
    output logic [7:0] sum_out_o
);
    parameter NUM_ADDERS = 4;
    genvar i;
    localparam START_VAL = 10;
    logic [7:0] local_sums [NUM_ADDERS-1:0];
    (* public *) logic [7:0] my_public_var;
    generate
        if (NUM_ADDERS > 0) begin : gen_if_block
            for (i = 0; i < NUM_ADDERS; i++) begin : gen_for_loop
                function automatic int calculate_per_instance(int current_i, int s_in);
                    return (current_i * s_in) + START_VAL;
                endfunction
                always_comb begin
                    local_sums[i] = calculate_per_instance(i, select_i);
                end
            end
        end else begin : gen_else_block
            always_comb begin
                local_sums[0] = 0;
            end
        end
    endgenerate
    always_comb begin
        my_public_var = 8'hAA;
        sum_out_o = '0;
        if (enable_i) begin
            for (int k=0; k<NUM_ADDERS; k++) begin
                sum_out_o += local_sums[k];
            end
        end
    end
endmodule
module LetAndDPIModule (
    input int a_in,
    input int b_in,
    output int result_out
);
    import "DPI-C" function int c_add(input int x, input int y);
    import "DPI-C" context function int c_multiply_context(input int x, input int y);
    (* verilator_public_task *) export "DPI-C" task my_exported_task;
    let sum_let(x, y) = x + y;
    let double_sum_let(x, y) = sum_let(x, y) + sum_let(x, y);
    function automatic int compute_result(int val1, int val2);
        int temp_sum;
        int temp_prod;
        temp_sum = sum_let(val1, val2);
        sum_let(val1, val2);
        temp_prod = c_multiply_context(val1, val2);
        return c_add(temp_sum, temp_prod);
    endfunction
    task my_exported_task();
    endtask
    always_comb begin
        result_out = compute_result(a_in, b_in);
    end
endmodule
module FileIOAndFormatModule (
    input bit [31:0] in_data_i,
    input string format_str_i,
    output int status_o,
    output logic [7:0] out_buf_o [3:0],
    output string sformat_out_o
);
    int scanned_val1, scanned_val2;
    string sscan_str = "Value1: 123 Value2: 456";
    int file_desc;
    initial begin
        status_o = 0;
        sformat_out_o = $sformatf(format_str_i, "String Arg", 123, 45.67, 8'hAB, status_o);
        sformat_out_o = $sformatf("Name: %m, Lib: %l, Escaped: %%, Ignore: %*d, Value: %d", 999);
        sformat_out_o = $sformatf("%s", "Direct string format literal");
        sformat_out_o = $sformatf("%0d %1d %.2d %-3d", 1,2,3,4);
        sformat_out_o = $sformatf("More arguments than format specifiers: %d", 10, 20, 30);
        status_o = $sscanf(sscan_str, "Value1: %d Value2: %d", scanned_val1, scanned_val2);
        out_buf_o[0] = scanned_val1;
        out_buf_o[1] = scanned_val2;
        out_buf_o[2] = '0;
        out_buf_o[3] = '0;
        file_desc = $fopen("temp.txt", "w");
        if (file_desc) begin
            $fdisplay(file_desc, "Test data for file ops");
            status_o = $ferror(file_desc);
            status_o = $fread(scanned_val1, file_desc);
            status_o = $feof(file_desc);
            $fclose(file_desc);
        end
    end
endmodule
module AssertionAndCoverageModule (
    input bit clk_i,
    input bit data_in_i,
    output logic assert_pass_o
);
    logic state;
    always_ff @(posedge clk_i) begin
        state <= data_in_i;
    end
    assert property (@(posedge clk_i) (data_in_i) |-> (state == 1'b1)) begin
        assert_pass_o = 1'b1;
    end else begin
        assert_pass_o = 1'b0;
    end
    assert property (@(posedge clk_i) (state == 1'b0) |-> (!data_in_i)) begin
    end
    (* verilator_coverage_block_off *)
    always_comb begin
        logic temp_val = data_in_i & state;
    end
endmodule
module UDPAndInterfaceModule (
    input bit i_clk,
    input bit i_a,
    input bit i_b,
    output bit o_y,
    output bit o_data_out,
    output bit o_valid_out
);
    my_and_udp u_and_gate (
        .Y(o_y),
        .A(i_a),
        .B(i_b)
    );
    my_interface ifc_inst(.clk(i_clk));
    always_comb begin
        ifc_inst.MASTER.data = i_a & i_b;
        ifc_inst.MASTER.valid = i_a | i_b;
        o_data_out = ifc_inst.SLAVE.data;
        o_valid_out = ifc_inst.SLAVE.valid;
    end
endmodule
interface my_interface(input bit clk);
    logic data;
    logic valid;
    modport MASTER (
        output data,
        output valid,
        input clk
    );
    modport SLAVE (
        input data,
        input valid,
        input clk
    );
endinterface
primitive my_and_udp (output Y, input A, B);
    table
      0 0 : 0;
      0 1 : 0;
      1 0 : 0;
      1 1 : 1;
    endtable
endprimitive
module CaseItemModule (
    input logic [1:0] sel_i,
    input logic [7:0] val1_i,
    input logic [7:0] val2_i,
    input logic [7:0] val3_i,
    output logic [7:0] result_o
);
    always_comb begin
        case (sel_i)
            2'b00: begin
                result_o = val1_i;
            end
            default: begin
                result_o = '0;
            end
            2'b01: begin
                result_o = val2_i;
            end
            2'b10: begin
                result_o = val3_i;
            end
        endcase
    end
endmodule
module HierarchyAndPublicityModule (
    input bit clk_i,
    output logic data_out_o
);
    ChildModule u_child (
        .clk_i(clk_i),
        .data_in_i(clk_i),
        .data_out_o(data_out_o)
    );
endmodule
(* verilator_public_module *)
module ChildModule (
    input bit clk_i,
    input bit data_in_i,
    output logic data_out_o
);
    always_comb begin
        data_out_o = data_in_i;
    end
endmodule
