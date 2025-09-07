package splitvar_examples_pkg;
  typedef struct packed {
    logic        a;
    logic [2:0]  b;
  } packed_s;
  typedef struct {
    logic [1:0]  x;
    logic        y;
  } unpacked_s;
endpackage
module mod_split_unpacked_array (
    input  logic [1:0] in0,
    input  logic [1:0] in1,
    output logic [1:0] out0
);
    import splitvar_examples_pkg::*;
    logic [1:0] arr [0:1] /*verilator split_var*/;
    always_comb begin
        arr[0]      = in0;
        arr[1][0]   = arr[0][0];
        arr[1][1]   = ~arr[0][1];
        out0        = arr[1];
    end
endmodule
module mod_split_packed_vector (
    input  logic        some_cond,
    input  logic        some_input0,
    input  logic [2:0]  some_input1,
    output logic [3:0]  packed_out
);
    logic [3:0] packed_var /*verilator split_var*/;
    always_comb begin
        if (some_cond) begin
            packed_var = 4'b0;
        end else begin
            packed_var[3]   = some_input0;
            packed_var[2:0] = some_input1;
        end
        packed_out = packed_var;
    end
endmodule
module mod_split_packed_struct (
    input  logic        sel,
    input  logic [2:0]  dat,
    output logic [3:0]  packed_vec_out
);
    import splitvar_examples_pkg::*;
    packed_s ps /*verilator split_var*/;
    always_comb begin
        ps.a = sel;
        ps.b = dat;
        packed_vec_out = {ps.a, ps.b};
    end
endmodule
module mod_unpacked_struct (
    input  logic        sel,
    output logic [2:0]  out_vec
);
    import splitvar_examples_pkg::*;
    unpacked_s us_arr [0:1] /*verilator split_var*/;
    always_comb begin
        us_arr[0].x = 2'b11;
        us_arr[0].y = sel;
        us_arr[1]   = us_arr[0];
        out_vec     = {us_arr[1].x, us_arr[1].y};
    end
endmodule
module mod_task_ref (
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    logic [7:0] foo /*verilator split_var*/;
    always_comb begin
        foo = in_data;
        modify(foo);
        out_data = foo;
    end
    task automatic modify (ref logic [7:0] a);
        a = ~a;
    endtask
endmodule
module mod_inout_port (
    inout  wire [7:0] bus /*verilator split_var*/,
    input  wire       ctrl,
    output wire       out0
);
    assign bus = ctrl ? 8'hFF : 8'hZZ;
    assign out0 = bus[0];
endmodule
module mod_public_cannot_split (
    input  logic [3:0] in_data,
    output logic [3:0] out_data
);
    logic [3:0] pubvar /*verilator split_var*/ /*verilator public*/;
    always_comb begin
        pubvar  = in_data;
        out_data = pubvar ^ in_data;
    end
endmodule
