interface simple_ifc (input logic clk);
    logic data;
    modport master (input  clk, output data);
    modport slave  (input  clk, input  data);
endinterface
module child_mod #(parameter WIDTH = 4) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    assign out = in;
endmodule
module complex_begin_module (
    input  logic [3:0] din,
    output logic [3:0] dout_func,
    output logic [3:0] dout_task
);
    logic [3:0] tmp_wire;
    begin : outer_scope
        function automatic logic [3:0] incr (input logic [3:0] val);
            static logic [3:0] acc = 4'h0;
            acc = acc + val;
            return acc;
        endfunction
        begin : inner_cell_block
            child_mod #(.WIDTH(4)) u_child (
                .in  (din),
                .out (tmp_wire)
            );
        end
    end
    begin : task_scope
        task automatic tally (input logic [3:0] val, output logic [3:0] res);
            static logic [3:0] cnt = 4'h0;
            cnt = cnt + val;
            res = cnt;
        endtask
    end
    assign dout_func = outer_scope.incr(tmp_wire);
    always_comb begin : tally_block
        task_scope.tally(din, dout_task);
    end
endmodule
module foreach_fixed_module (
    input  logic [7:0] in_val,
    output logic [7:0] sum
);
    logic [7:0] array_fixed [0:3];
    always_comb begin : accumulate
        array_fixed[0] = in_val;
        array_fixed[1] = in_val + 8'd1;
        array_fixed[2] = in_val + 8'd2;
        array_fixed[3] = in_val + 8'd3;
        sum = 8'd0;
        foreach (array_fixed[idx]) begin
            sum += array_fixed[idx];
        end
    end
endmodule
module string_foreach_module (
    input  logic       dummy_in,
    output logic [7:0] last_char
);
    string str;
    always_comb begin : str_loop
        int i;
        last_char = 8'd0;
        str = "verilator";
        foreach (str[i]) begin
            last_char = str[i];
        end
    end
endmodule
module assoc_foreach_module (
    input  logic  [7:0] in_byte,
    output logic [15:0] total
);
    typedef int unsigned amap_t [string];
    amap_t amap;
    always_comb begin : assoc_loop
        string key;
        amap        = '{default:0};
        amap["a"]   = 1;
        amap["b"]   = in_byte;
        total = 16'd0;
        foreach (amap[key]) begin
            total += amap[key];
        end
    end
endmodule
module fork_begin_module (
    input  logic in_sig,
    output logic out_sig
);
    always @(*) begin
        fork
            begin : blk1
                out_sig = in_sig;
            end
        join
    end
endmodule
module deep_if_module (
    input  logic [3:0] din,
    output logic       dout
);
    always_comb begin
        dout = 1'b0;
        if (din[3]) begin
            if (din[2]) begin
                if (din[1]) begin
                    if (din[0]) begin
                        dout = 1'b1;
                    end
                end
            end
        end
    end
endmodule
module interface_scope_module (
    input  logic clk,
    input  logic in_data,
    output logic out_data
);
    begin : iface_scope
        simple_ifc intf_inst (.clk(clk));
        assign intf_inst.data = in_data;
        assign out_data       = intf_inst.data;
    end
endmodule
