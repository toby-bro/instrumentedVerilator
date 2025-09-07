primitive combo_mux (
  input sel,
  input in0,
  input in1,
  output out
);
  table
     0    0    ?  : 0;
     0    1    ?  : 1;
     1    ?    0  : 0;
     1    ?    1  : 1;
     ?    ?    ?  : x; 
  endtable
endprimitive
primitive seq_dff_rst (
  output q, 
  input clk,
  input rst_n,
  input data_in
);
  reg q; 
  initial q = 1'b0; 
  table
      ?      ?     0     ?    : 0;   
      0      p     1     0    : 0;   
      0      p     1     1    : 1;   
      1      p     1     0    : 0;
      1      p     1     1    : 1;
      ?      n     1     ?    : -;   
      ?      *     1     ?    : -;   
      ?      (01)  1     ?    : -;   
      ?      (10)  1     ?    : -;   
      ?      (r)   1     ?    : -;   
      ?      (P)   1     ?    : -;   
      ?      (R)   1     ?    : -;   
      ?      (f)   1     ?    : -;   
      ?      (N)   1     ?    : -;   
      ?      (F)   1     ?    : -;   
  endtable
endprimitive
primitive logic_gate (
  input a,
  input b,
  input c,
  output out
);
  table
     0 0 0 : 1;
     0 0 1 : 0;
     0 1 0 : 0;
     0 1 1 : 1;
     1 0 0 : 0;
     1 0 1 : 1;
     1 1 0 : 1;
     1 1 1 : 0;
     x x x : x; 
     0 1 b : x; 
  endtable
endprimitive
primitive seq_edge_test (
  output state_out, 
  input clk_in,
  input set_n_in
);
  reg state_out; 
  initial state_out = 1'b0;
  table
      ?          ?        0     : 1;  
      0          (r)      1     : 1;  
      1          (f)      1     : 0;  
      0          (R)      1     : 1;  
      1          (F)      1     : 0;  
      0          (p)      1     : 1;  
      1          (n)      1     : 0;  
      ?          *        1     : -;  
      ?          ?        ?     : -;  
  endtable
endprimitive
primitive test_edge_misc_inputs (
  output qout, 
  input clki,
  input datai,
  input reseti
);
  reg qout;
  initial qout = 1'bx; 
  table
      ?    *     ?     ?    : -;  
      ?    (p)   ?     ?    : -;  
      ?    (n)   ?     ?    : -;  
      ?    (r)   ?     ?    : -;  
      ?    (f)   ?     ?    : -;  
      ?    (P)   ?     ?    : -;  
      ?    (N)   ?     ?    : -;  
      ?    (R)   ?     ?    : -;  
      ?    (F)   ?     ?    : -;  
      ?    (01)  ?     ?    : -;  
      ?    (10)  ?     ?    : -;  
      ?    x     ?     0    : 0;  
      ?    ?     0     1    : 0;  
      ?    ?     1     1    : 1;  
  endtable
endprimitive
