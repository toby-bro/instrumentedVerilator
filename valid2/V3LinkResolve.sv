interface my_if;
    logic a;
    modport P (input a);
endinterface
primitive udp_and (out, in1, in2);
    output out;
    input  in1, in2;
    table
        0 0 : 0;
        0 1 : 0;
        1 0 : 0;
        1 1 : 1;
    endtable
endprimitive
module mod_pragmas
(
    input  logic [3:0] in_data,
    output logic [3:0] out_data
);
    task automatic do_shift(input logic [3:0] din, output logic [3:0] dout);
        dout = {din[2:0], din[3]};
    endtask
    always_comb begin
        do_shift(in_data, out_data);
    end
    property p_shift_ok;
        @(posedge in_data[0]) out_data != 4'h0;
    endproperty
    assert property (p_shift_ok);
endmodule
module mod_class_features
(
    input  logic        clk,
    input  logic [3:0]  in1,
    output logic [7:0]  out1
);
    class myc;
        rand bit [3:0] a;
        rand bit [3:0] b;
        constraint c_dist { a dist { [0:3] :/ 1, [4:15] :/ 2 }; }
        constraint c_soft { soft a inside {4'h5, 4'h6}; }
        function int getVal();
            return a;
        endfunction
    endclass
    let add4(x, y) = x + y + 4;
    logic [3:0] tmp4;
    always_comb begin
        if (in1 != 0) begin
            tmp4 = add4(in1, 4'd0);
        end else begin
            tmp4 = 4'd0;
        end
    end
    always_ff @(posedge clk) begin
        myc inst = new();
        void'(inst.randomize());
        out1 <= {4'h0, tmp4};
    end
    assert property (@(posedge clk) out1[7:4] == 0);
endmodule
module mod_generate_blocks
(
    input  logic [3:0] in_sig,
    output logic [3:0] out_sig
);
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : g_loop
            if (i % 2 == 0) begin : g_if
                always_comb out_sig[i] = in_sig[3 - i];
            end else begin : g_else
                always_comb out_sig[i] = in_sig[i];
            end
        end
    endgenerate
endmodule
module mod_initial_auto
(
    input  logic i,
    output logic o
);
    logic tmp;
    initial begin : init_blk
        tmp = i;
        o   = tmp;
    end
endmodule
module mod_file_ops
(
    input  logic clk,
    input  logic req,
    output logic done
);
    integer fd;
    integer r;
    integer val;
    reg [7:0] mem [0:15];
    string    str;
    always_ff @(posedge clk) begin
        if (req) begin
            fd   <= 32'd1;
            done <= 0;
            r    <= $ferror(fd, val);
            r    <= $feof(fd);
            r    <= $fread(mem, fd);
            $fclose(fd);
            r    <= $fscanf(fd, "%d", val);
            str  <= $sformatf("%0d", val);
            r    <= $sscanf(str, "%d", val);
            done <= 1;
        end
    end
endmodule
module mod_case_default
(
    input  logic [1:0] sel,
    input  logic [3:0] data_in,
    output logic [3:0] data_out
);
    always_comb begin
        case (sel)
            2'd0   : data_out = data_in;
            default: data_out = 4'h0;
            2'd1   : data_out = 4'h1;
        endcase
    end
endmodule
module mod_interface_dtype
(
    input  logic dummy_in,
    output logic dummy_out
);
    virtual my_if.P vip;
    assign dummy_out = dummy_in;
endmodule
