module unpacked_array1(
  input logic [1:0] inarr [0:1] /*verilator split_var*/,
  output logic [1:0] outarr [0:1]
);
  always_comb begin
    outarr[1][0] = inarr[0][0];
    outarr[1][1] = ~inarr[0][1];
  end
endmodule
module packed_var1(
  input logic cond,
  input logic input0,
  input logic [2:0] input1,
  output logic [3:0] packed_var /*verilator split_var*/
);
  always_comb begin
    if (cond)
      packed_var = 4'b0;
    else begin
      packed_var[3]   = input0;
      packed_var[2:0] = input1;
    end
  end
endmodule
module nested_unpacked(
  input logic [1:0] arr [0:1] /*verilator split_var*/,
  output logic val
);
  always_comb val = arr[1][0] & arr[0][1];
endmodule
module nested2_unpacked(
  input logic [1:0] arr [0:1] [0:1] /*verilator split_var*/,
  output logic bit0,
  output logic bit1
);
  always_comb begin
    bit0 = arr[1][0][0];
    bit1 = arr[0][1][1];
  end
endmodule
module bitfield_split(
  input logic [7:0] bf /*verilator split_var*/,
  output logic [3:0] low,
  output logic [3:0] high
);
  always_comb begin
    low  = bf[3:0];
    high = bf[7:4];
  end
endmodule
module unpacked_struct_split(us_arr, a0, b1);
  typedef struct { logic [1:0] a; logic b; } us_t;
  input us_t us_arr [0:1] /*verilator split_var*/;
  output logic [1:0] a0;
  output logic b1;
  always_comb begin
    a0 = us_arr[1].a;
    b1 = us_arr[0].b;
  end
endmodule
module packed_struct_split(
  input logic [1:0] in1,
  input logic in2,
  output logic [1:0] outc,
  output logic outd
);
  typedef struct packed { logic [1:0] c; logic d; } ps_t;
  ps_t sp /*verilator split_var*/;
  always_comb begin
    sp.c = in1;
    sp.d = in2;
    outc = sp.c;
    outd = sp.d;
  end
endmodule
module task_split(
  input logic [1:0] a [0:1] /*verilator split_var*/,
  output logic [1:0] result
);
  task tsk(input logic [1:0] arr [0:1] /*verilator split_var*/, output logic [1:0] res);
    res = arr[1] ^ arr[0];
  endtask
  always_comb begin
    result = a[1] & a[0];
    tsk(a, result);
  end
endmodule
module func_split(
  input logic [3:0] in,
  output logic [3:0] out
);
  function automatic logic [3:0] fcn(input logic [3:0] v /*verilator split_var*/);
    fcn = v + 1;
  endfunction
  always_comb out = fcn(in);
endmodule
module concat_split(
  input logic [1:0] a,
  input logic [1:0] b,
  output logic [3:0] c /*verilator split_var*/
);
  always_comb c = {a, b};
endmodule
