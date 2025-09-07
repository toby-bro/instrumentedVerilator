module randcase_demo(input logic enable, input logic [1:0] selector, output logic [3:0] result);
  always_comb begin
    result = 0;
    if (enable) begin
      randcase
        1: result = 1;
        2: result = 2;
        3: result = 3;
      endcase
    end
  end
endmodule
module dynamic_array_demo(input logic do_rand, input int size, output logic [7:0] out_data);
  class DynArrayClass;
    rand logic [7:0] data[];
    constraint len_c { data.size() == size; }
  endclass
  DynArrayClass dac;
  always_comb begin
    dac = new;
    dac.data = new[size];
    if (do_rand)
      dac.randomize() with { dac.data.size() == size; };
    out_data = dac.data[0];
  end
endmodule
module queue_rand_demo(input logic go, input int len, output logic [7:0] out0, output int qsize);
  class QueueClass;
    rand byte q_queue[$];
    constraint qlen_c { q_queue.size() == len; }
  endclass
  QueueClass qc;
  always_comb begin
    qc = new;
    if (go) begin
      qc.q_queue = new[len];
      qc.randomize();
    end
    qsize = qc.q_queue.size();
    out0 = qc.q_queue[0];
  end
endmodule
module struct_rand_demo(input logic do_rand, output logic [3:0] a_out);
  typedef struct packed { rand logic [3:0] a; logic [3:0] b; } MyStruct;
  class StructClass;
    rand MyStruct s;
    constraint sb_c { s.b == s.a + 1; }
  endclass
  StructClass sc;
  always_comb begin
    sc = new;
    if (do_rand) sc.randomize();
    a_out = sc.s.a;
  end
endmodule
module union_rand_demo(input logic start, output logic [3:0] u_out);
  typedef union packed { rand logic [3:0] u; logic [3:0] v; } MyUnion;
  class UnionClass;
    rand MyUnion uu;
  endclass
  UnionClass uc;
  always_comb begin
    uc = new;
    if (start) uc.randomize();
    u_out = uc.uu.u;
  end
endmodule
module assoc_array_demo(input logic do_rand, input string key, output logic [7:0] data_out);
  class AssocClass;
    rand logic [7:0] mem[string];
    constraint key_c { foreach (mem[i]) i.len() > 0; }
  endclass
  AssocClass ac;
  always_comb begin
    ac = new;
    if (do_rand) ac.randomize();
    if (ac.mem.exists(key))
      data_out = ac.mem[key];
    else
      data_out = 0;
  end
endmodule
module foreach_demo(input logic run, input int size, output logic [6:0] val_out);
  class ForEachClass;
    rand logic [6:0] arr[];
    constraint arr_c { foreach (arr[i]) arr[i] < 64; }
  endclass
  ForEachClass fc;
  always_comb begin
    fc = new;
    fc.arr = new[size];
    if (run) fc.randomize();
    val_out = fc.arr[0];
  end
endmodule
module unique_demo(input logic run, output logic [3:0] v0, output logic [3:0] v1, output logic [3:0] v2);
  class UniqueClass;
    rand logic [3:0] arr[4];
    constraint uniq_c { unique { arr }; }
  endclass
  UniqueClass uc;
  always_comb begin
    uc = new;
    if (run) uc.randomize();
    v0 = uc.arr[0];
    v1 = uc.arr[1];
    v2 = uc.arr[2];
  end
endmodule
module randc_demo(input logic start, output logic [2:0] outc);
  class RandcClass;
    randc logic [2:0] rc;
  endclass
  RandcClass rc_h;
  always_comb begin
    rc_h = new;
    if (start) rc_h.randomize();
    outc = rc_h.rc;
  end
endmodule
module inheritance_demo(input logic start, output logic [7:0] val, output logic [7:0] extra);
  class Base;
    rand logic [7:0] val;
  endclass
  class Derived extends Base;
    rand logic [7:0] extra;
    constraint sum_c { val + extra < 255; }
  endclass
  Derived d;
  always_comb begin
    d = new;
    if (start) d.randomize();
    val = d.val;
    extra = d.extra;
  end
endmodule
module inline_rand_demo(input logic go, output int a_out, output int b_out);
  class InlineClass;
    rand int a; rand int b;
  endclass
  InlineClass ic;
  always_comb begin
    ic = new;
    if (go)
      ic.randomize() with { ic.a < ic.b; };
    a_out = ic.a;
    b_out = ic.b;
  end
endmodule
module bit_select_demo(input logic do_rand, output logic [3:0] nibble);
  class BitSelClass;
    rand logic [7:0] x;
    constraint low_c { x[3:0] == 4'hA; }
  endclass
  BitSelClass bs;
  always_comb begin
    bs = new;
    if (do_rand) bs.randomize();
    nibble = bs.x[3:0];
  end
endmodule
