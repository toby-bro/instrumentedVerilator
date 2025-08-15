primitive comb_logic_udp (
  output out_c,
  input  in_a,
  input  in_b
);
  table
     0    0    : 0;
     0    1    : 1;
     1    0    : 1;
     1    1    : x;
     ?    0    : 0;
     0    ?    : 0;
     1    ?    : x;
     ?    1    : x;
     ?    ?    : 0;
  endtable
endprimitive
primitive comb_pos_map_udp (
  output out_pos,
  input  in_pos
);
  table
    0 : 0;
    1 : 1;
    ? : x;
  endtable
endprimitive
primitive comb_neg_map_udp (
  output out_neg,
  input  in_neg
);
  table
    0 : 1;
    1 : 0;
    ? : x;
  endtable
endprimitive
primitive comb_any_map_udp (
  output out_any,
  input  in_any
);
  table
    0 : 0;
    1 : 1;
    ? : X;
  endtable
endprimitive
primitive multi_input_comb_udp (
  output out_val,
  input  in1,
  input  in2,
  input  in3
);
  table
     0   0   0   : 0;
     0   0   1   : 1;
     0   1   0   : 1;
     0   1   1   : x;
     1   0   0   : 1;
     1   0   1   : x;
     1   1   0   : 0;
     1   1   1   : 1;
     ?   ?   ?   : x;
  endtable
endprimitive
primitive simple_one_bit_udp (
  output o_val,
  input  i_val
);
  table
     0   : 1;
     1   : 0;
  endtable
endprimitive
primitive d_ff_seq_udp (
  output reg q_out,
  input  d_in,
  input  clk_in,
  input  reset_in
);
  initial q_out = 1'b0;
  table
    ?    ?      1        : ?     : 0;
    0    (01)   0        : ?     : 0;
    1    (01)   0        : ?     : 1;
    x    (01)   0        : ?     : x; 
    ?    0      0        : ?     : -; 
    ?    1      0        : ?     : -; 
    ?    x      0        : ?     : -; 
    0    p      0        : ?     : 0; 
    1    r      0        : ?     : 1; 
    0    n      0        : ?     : 0; 
    1    f      0        : ?     : 1; 
    x    *      0        : ?     : x; 
  endtable
endprimitive
primitive seq_edge_variant_udp (
  output reg out_q,
  input      in_d,
  input      in_clk
);
  initial out_q = 1'b0;
  table
    0 (00) : ? : 0; 
    1 (11) : ? : 1; 
    x (0?) : ? : x; 
    x (?0) : ? : x; 
    x (1?) : ? : x; 
    x (?1) : ? : x; 
    x (??) : ? : x; 
  endtable
endprimitive
primitive seq_no_change_udp (
  output reg out_q,
  input      in_data,
  input      in_clock
);
  initial out_q = 1'b0;
  table
    0 (01) : 0 : -; 
    1 (01) : 1 : -; 
    0 (01) : 1 : 0; 
    1 (01) : 0 : 1; 
    x (10) : ? : -; 
  endtable
endprimitive
