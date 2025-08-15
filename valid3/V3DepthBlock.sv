class SimpleClass;
  int data;
  function new(int v = 0);
    data = v;
  endfunction
  function void set(int v);
    data = v;
  endfunction
  function int get();
    return data;
  endfunction
endclass
typedef struct packed {
  logic [7:0] a;
  logic [7:0] b;
} my_struct_t;
typedef union packed {
  logic [15:0] whole;
  struct packed {
    logic [7:0] lo;
    logic [7:0] hi;
  } parts;
} my_union_t;
//----------------------------------------------------------------------
module deep_if_module(input  logic [31:0] in_val,
                      output logic [31:0] out_val);
  always_comb begin : proc_deep_if
    logic [31:0] tmp;
    tmp = in_val;
    if (tmp[0]) begin
      tmp = tmp + 1;
      if (tmp[1]) begin
        tmp = tmp + 1;
        if (tmp[2]) begin
          tmp = tmp + 1;
          if (tmp[3]) begin
            tmp = tmp + 1;
            if (tmp[4]) begin
              tmp = tmp + 1;
              if (tmp[5]) begin
                tmp = tmp + 1;
                if (tmp[6]) begin
                  tmp = tmp + 1;
                  if (tmp[7]) begin
                    tmp = tmp + 1;
                    if (tmp[8]) begin
                      tmp = tmp + 1;
                      if (tmp[9]) begin
                        tmp = tmp + 1;
                        if (tmp[10]) begin
                          tmp = tmp + 1;
                          if (tmp[11]) begin
                            tmp = tmp + 1;
                            if (tmp[12]) begin
                              tmp = tmp + 1;
                              if (tmp[13]) begin
                                tmp = tmp + 1;
                                if (tmp[14]) begin
                                  tmp = tmp + 1;
                                  if (tmp[15]) begin
                                    tmp = tmp + 1;
                                    if (tmp[16]) begin
                                      tmp = tmp + 1;
                                      if (tmp[17]) begin
                                        tmp = tmp + 1;
                                        if (tmp[18]) begin
                                          tmp = tmp + 1;
                                          if (tmp[19]) begin
                                            tmp = tmp + 1;
                                            if (tmp[20]) begin
                                              tmp = tmp + 1;
                                              if (tmp[21]) begin
                                                tmp = tmp + 1;
                                                if (tmp[22]) begin
                                                  tmp = tmp + 1;
                                                  if (tmp[23]) begin
                                                    tmp = tmp + 1;
                                                    if (tmp[24]) begin
                                                      tmp = tmp + 1;
                                                      if (tmp[25]) begin
                                                        tmp = tmp + 1;
                                                        if (tmp[26]) begin
                                                          tmp = tmp + 1;
                                                          if (tmp[27]) begin
                                                            tmp = tmp + 1;
                                                            if (tmp[28]) begin
                                                              tmp = tmp + 1;
                                                              if (tmp[29]) begin
                                                                tmp = tmp + 1;
                                                                if (tmp[30]) begin
                                                                  tmp = tmp + 1;
                                                                  if (tmp[31]) begin
                                                                    tmp = tmp + 1;
                                                                  end
                                                                end
                                                              end
                                                            end
                                                          end
                                                        end
                                                      end
                                                    end
                                                  end
                                                end
                                              end
                                            end
                                          end
                                        end
                                      end
                                    end
                                  end
                                end
                              end
                            end
                          end
                        end
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end
    end
    out_val = tmp;
  end
endmodule
//----------------------------------------------------------------------
module deep_loop_module(input  logic enable,
                        output logic [7:0] o);
  always_comb begin : proc_deep_loop
    int sum;
    sum = 0;
    if (enable) begin
      int i;
      for (i = 0; i < 100; i++) begin
        if (i == 50) begin
          break;
        end else begin
          sum = sum + i;
          if (i & 1) begin
            continue;
          end
          sum = sum + 1;
        end
      end
    end
    o = sum[7:0];
  end
endmodule
//----------------------------------------------------------------------
module deep_case_module(input  logic [3:0]  sel,
                        input  logic [31:0] in_data,
                        output logic [31:0] out_data);
  always_comb begin : proc_deep_case
    case (sel)
      4'd0: out_data = in_data;
      4'd1: out_data = {in_data[15:0], in_data[31:16]};
      4'd2: out_data = ~in_data;
      4'd3: begin
        case (in_data[1:0])
          2'd0: out_data = in_data + 1;
          2'd1: out_data = in_data + 2;
          2'd2: out_data = in_data + 3;
          default: out_data = in_data + 4;
        endcase
      end
      default: out_data = 32'hDEADBEEF;
    endcase
  end
endmodule
//----------------------------------------------------------------------
module deep_func_module(input  logic [15:0] a,
                        output logic [15:0] y);
  function automatic logic [15:0] complex_calc(input logic [15:0] v);
    int i;
    complex_calc = v;
    for (i = 0; i < 16; i++) begin
      complex_calc = (complex_calc << 1) ^ (complex_calc >> 1);
    end
  endfunction
  assign y = complex_calc(a);
endmodule
//----------------------------------------------------------------------
module deep_expr_module(input  logic [31:0] x,
                        output logic [31:0] y);
  assign y = (((((((((((((((((((((((((x + 1) + 2) + 3) + 4) + 5) + 6) + 7) + 8) + 9) + 10)
               + 11) + 12) + 13) + 14) + 15) + 16) + 17) + 18) + 19) + 20) + 21) + 22) + 23) + 24) + 25);
endmodule
//----------------------------------------------------------------------
module class_use_module(input  logic [7:0] val,
                        output logic [7:0] res);
  always_comb begin : proc_class_use
    SimpleClass obj = new(val);
    obj.set(val + 1);
    res = obj.get()[7:0];
  end
endmodule
//----------------------------------------------------------------------
module deep_while_module(input  logic en,
                         output logic [7:0] outv);
  always_comb begin : proc_deep_while
    int cnt;
    cnt = 0;
    while (cnt < 20) begin
      if (cnt == 10) begin
        cnt = cnt + 2;
      end else begin
        cnt = cnt + 1;
      end
    end
    outv = cnt[7:0];
  end
endmodule
//----------------------------------------------------------------------
module generate_param_module#(parameter WIDTH = 8)
                             (input  logic [WIDTH-1:0] in_data,
                              output logic [WIDTH-1:0] out_data);
  generate
    if (WIDTH > 16) begin : wide_block
      assign out_data = in_data & {WIDTH{1'b1}};
    end else begin : narrow_block
      assign out_data = ~in_data;
    end
  endgenerate
endmodule
//----------------------------------------------------------------------
module labeled_block_module(input  logic [3:0] idx,
                            output logic [3:0] result);
  always_comb begin : main_block
    result = idx;
    begin : nested1
      result = result + 1;
      begin : nested2
        result = result ^ 4'h3;
      end
    end
  end
endmodule
//----------------------------------------------------------------------
module array_assign_module(input  logic [7:0] a_in,
                           output logic [7:0] a_out);
  logic [7:0] arr [0:3];
  always_comb begin : proc_array
    arr[0] = a_in;
    arr[1] = a_in + 1;
    arr[2] = arr[0] ^ arr[1];
    arr[3] = arr[2] - a_in;
    a_out  = arr[3];
  end
endmodule
//----------------------------------------------------------------------
module struct_module(input  my_struct_t s_in,
                     output my_struct_t s_out);
  always_comb begin : proc_struct
    s_out.a = s_in.a + s_in.b;
    s_out.b = s_in.b - s_in.a;
  end
endmodule
//----------------------------------------------------------------------
module union_module(input  my_union_t u_in,
                    output my_union_t u_out);
  always_comb begin : proc_union
    u_out.whole = u_in.parts.lo + u_in.parts.hi;
  end
endmodule
//----------------------------------------------------------------------
module enum_module(input  logic [1:0] sel,
                   output logic flag);
  typedef enum logic [1:0] {IDLE = 2'd0, RUN = 2'd1, STOP = 2'd2} state_t;
  state_t st;
  always_comb begin
    st   = state_t'(sel);
    flag = (st == RUN);
  end
endmodule
//----------------------------------------------------------------------
module rand_module(input  logic [7:0] seed,
                   output logic [7:0] rnd);
  always_comb begin
    rnd = $urandom(seed);
  end
endmodule
//----------------------------------------------------------------------
module assert_module(input  logic a,
                     input  logic b,
                     output logic out);
  always_comb begin
    out = a & b;
    assert (a | b) else out = 1'b0;
  end
endmodule
