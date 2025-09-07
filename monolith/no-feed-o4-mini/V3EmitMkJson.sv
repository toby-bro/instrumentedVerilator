class Processor;
   function logic [7:0] compute(input logic [7:0] x, input logic flag);
      if (flag) compute = x + 1;
      else compute = x - 1;
   endfunction
endclass
module static_function_module(input logic [7:0] a, input logic en, output logic [7:0] b);
   static function automatic logic [7:0] doubleVal(input logic [7:0] x);
      return x << 1;
   endfunction
   always_comb begin
      if (en)
         b = static_function_module::doubleVal(a);
      else
         b = a;
   end
endmodule
module class_method_module(input logic clk, input logic [7:0] in, input logic flag, output logic [7:0] out);
   Processor proc_h;
   always_ff @(posedge clk) begin
      proc_h = new();
      out = proc_h.compute(in, flag);
   end
endmodule
module dynamic_array_module(input logic clk, input logic rst, output int sum_out);
   int dyn_arr[];
   int sum;
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
         dyn_arr = new[1];
         dyn_arr[0] = 0;
         sum = 0;
      end else begin
         int new_size = dyn_arr.size() + 1;
         int temp[];
         temp = dyn_arr;
         dyn_arr = new[new_size];
         foreach (temp[i]) dyn_arr[i] = temp[i];
         dyn_arr[new_size-1] = new_size;
         sum = 0;
         foreach (dyn_arr[i]) sum += dyn_arr[i];
      end
   end
   assign sum_out = sum;
endmodule
module string_array_module(input logic en, output string combined);
   string sarr[];
   always_comb begin
      sarr = new[3];
      sarr[0] = "one";
      sarr[1] = "two";
      sarr[2] = "three";
      combined = "";
      if (en) begin
         foreach (sarr[i]) combined = {combined, sarr[i], "_"};
      end else combined = "disabled";
   end
endmodule
module associative_array_module(input logic clk, input logic set, input string key, input int value, output int out_value);
   int amap[string];
   always_ff @(posedge clk) begin
      if (set) amap[key] = value;
   end
   always_comb begin
      if (amap.exists(key)) out_value = amap[key];
      else out_value = -1;
   end
endmodule
module queue_module(input logic clk, input logic enqueue, input logic dequeue, input int in_val, output int out_val);
   integer q[$];
   integer out_tmp;
   always_ff @(posedge clk) begin
      if (enqueue) q.push_back(in_val);
      if (dequeue) begin
         if (q.size() > 0) out_tmp = q.pop_front();
         else out_tmp = 0;
      end else out_tmp = 0;
   end
   assign out_val = out_tmp;
endmodule
module parameterized_module #(parameter WIDTH = 8)(input logic [WIDTH-1:0] in, output logic [WIDTH-1:0] out);
   assign out = ~in;
endmodule
module generate_for_module(input logic [3:0] sel, output logic [3:0] out);
   genvar i;
   generate
      for (i = 0; i < 4; i++) begin : gen_loop
         assign gen_loop[i].out = sel[i] & (i % 2);
      end
   endgenerate
endmodule
module generate_if_module #(parameter USE_INVERT = 0)(input logic [7:0] in, output logic [7:0] out);
   generate
      if (USE_INVERT) begin
         assign out = ~in;
      end else begin
         assign out = in;
      end
   endgenerate
endmodule
module nested_block_module(input logic a, input logic b, input logic c, output logic y);
   always_comb begin
      if (a) begin
         if (b) begin
            y = c;
         end else begin
            y = ~c;
         end
      end else begin
         y = 1'b0;
      end
   end
endmodule
module typedef_module(input logic [1:0] sel, input logic [3:0] in, output logic [3:0] out);
   typedef logic [3:0] data_t;
   data_t arr[4];
   always_comb begin
      arr[0] = in;
      arr[1] = in << 1;
      arr[2] = in << 2;
      arr[3] = in << 3;
      out = arr[sel];
   end
endmodule
module static_var_module(input logic clk, input logic inc, output int cnt);
   function int counter(input logic incf);
      static int cvar = 0;
      if (incf) cvar++;
      return cvar;
   endfunction
   always_ff @(posedge clk) begin
      cnt <= counter(inc);
   end
endmodule
module function_with_default_module(input logic [7:0] a, input logic add_enable, output logic [7:0] b);
   function logic [7:0] adder(input logic [7:0] x, input logic [7:0] y = 8'h01);
      adder = x + y;
   endfunction
   always_comb begin
      if (add_enable) b = adder(a);
      else b = a;
   end
endmodule
module loop_break_continue(input logic start, output logic done);
   logic [7:0] cnt;
   always_comb begin
      cnt = 0;
      done = 0;
      for (int i = 0; i < 10; i++) begin
         if (!start) continue;
         cnt++;
         if (cnt == 5) begin
            done = 1;
            break;
         end
      end
   end
endmodule
