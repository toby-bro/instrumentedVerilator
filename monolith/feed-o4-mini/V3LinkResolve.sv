class RC;
  rand bit [3:0] a, rc;
  constraint c1 { a < 10; }
  constraint c2 { soft a > 2; }
  constraint d1 { dist a { [0:3] :/ 50, [4:7] :/ 50 }; }
  constraint sb { solve rc before a; }
  function new(); endfunction
endclass
module rc_inst_mod(input logic enable, output logic result);
  always_comb begin
    automatic RC c = new();
    c.randomize();
    result = c.a > c.rc;
  end
endmodule
module case_mod(input logic [1:0] sel, input logic a, input logic b, input logic c, output logic out);
  always_comb begin
    case (sel)
      2'b00: out = a;
      default: out = b;
      2'b10: out = c;
    endcase
  end
endmodule
module let_mod(input logic [3:0] in, output logic [3:0] out);
  let increment(x) = x + 1;
  assign out = increment(in);
endmodule
module file_ops(input logic [7:0] in, output logic [7:0] out);
  int file;
  string fmtstr;
  int scan_out;
  always_comb begin
    file = $fopen("dummy.txt", "r");
    fmtstr = $sformatf("Value:%0d", in);
    out = in;
    $fread(file, out);
    $fscanf(file, "%d", scan_out);
    scan_out = $feof(file);
    $ferror(file, scan_out);
    $fclose(file);
  end
endmodule
module sscan_mod(input logic [31:0] val_in, output logic [31:0] val_out);
  string str;
  always_comb begin
    str = "123";
    $sscanf(str, "%d", val_out);
  end
endmodule
module genfor_mod(input logic [3:0] in, output logic [3:0] out);
  logic [3:0] arr [1:0];
  genvar i;
  generate
    for (i = 0; i < 2; i++) begin : loop
      assign arr[i] = in + i;
    end
  endgenerate
  generate
    if (1) begin : cond
      assign out = arr[1];
    end
  endgenerate
endmodule
primitive udp2(y, a, b);
  output y;
  input a, b;
  table
    1 1 : 1;
    1 0 : 0;
    0 1 : 0;
    0 0 : 0;
  endtable
endprimitive
module udp_mod(input wire a, input wire b, output wire y);
  udp2 u2(y, a, b);
endmodule
module dpi_mod(input int in, output int out);
  import "DPI-C" function int cfunc(input int a);
  function int lf(input int a);
    lf = cfunc(a);
  endfunction
  task stsk(input int a);
  endtask
  export "DPI-C" task stsk;
  assign out = lf(in);
endmodule
module cov_mod(input logic clk, input logic sig, output logic out);
  covergroup cg @(posedge clk);
    cp: coverpoint sig;
  endgroup
  cg cg_inst = new();
  property p1; @(posedge clk) sig |-> out; endproperty
  assert property (p1);
  assign out = sig;
endmodule
