module cont_strength_assign(input  wire a, output wire b);
  assign (strong1, weak0) b = a;
endmodule
module prepost_sel(input  logic [7:0] in1, output logic [7:0] out1);
  always_comb begin
    logic [7:0] temp;
    temp = in1;
    ++temp;
    temp[3:0] = temp[7:4];
    out1 = temp;
  end
endmodule
module force_event_cast(input  logic in2, output logic out2);
  event e;
  logic tmp;
  int   result;
  always_comb begin
    result = 0;
    tmp = 0;
    force tmp = in2;
    release tmp;
    -> e;
    void'($cast(result, {tmp, in2}));
    out2 = result[0];
  end
endmodule
module file_ops(input  logic in3, output logic out3);
  int fh;
  string str;
  byte unsigned mem_buf [0:15];
  int i;
  always_comb begin
    fh = 0;
    i  = 0;
    $ferror(fh, i);
    i = $fgets(str, fh);
    i = $fread(mem_buf, fh);
    i = $fscanf(fh, "%s", str);
    i = $ungetc(8'h41, fh);
    i = $sscanf("123", "%d", i);
    out3 = in3 ^ i[0];
  end
endmodule
module readmem_mod(input  logic [7:0] addr, output logic [7:0] data);
  logic [7:0] mem [0:255];
  initial begin
    $readmemh("dummy.mem", mem);
  end
  always_comb begin
    data = mem[addr];
  end
endmodule
module plusargs_mod(input  logic in4, output logic out4);
  logic [31:0] val;
  always_comb begin
    val = 0;
    out4 = in4;
    if ($test$plusargs("TEST")) begin
      out4 = in4;
    end else begin
      void'($value$plusargs("VAL=%d", val));
      out4 = val[0];
    end
  end
endmodule
module sformat_mod(input  logic [3:0] in5, output logic [7:0] out5);
  string s;
  always_comb begin
    $sformat(s, "Val=%0d", in5);
    out5 = {4'b0, in5};
  end
endmodule
module ftask_call(input  logic [3:0] in7, output logic [3:0] out7);
  task automatic calc(output logic [3:0] o, input logic [3:0] i);
    o = i + 4'h1;
  endtask
  always_comb begin
    calc(out7, in7);
  end
endmodule
typedef struct packed { logic [3:0] a; logic [3:0] b; } my_struct_t;
module member_sel(input  logic [3:0] in8, output logic [3:0] out8);
  my_struct_t s;
  always_comb begin
    s.a = in8;
    s.b = ~in8;
    out8 = s.b;
  end
endmodule
module static_init(input  logic [3:0] in9, output logic [3:0] out9);
  function automatic logic [3:0] id(input logic [3:0] v);
    id = v;
  endfunction
  logic [3:0] s_var = 4'h0;
  always_comb begin
    s_var = id(in9);
    out9  = s_var;
  end
endmodule
