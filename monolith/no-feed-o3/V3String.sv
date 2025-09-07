module attr_escape_mod
  #(parameter string P_STR = "Line1\nLine2\t\101\012\x41 %%percent%%")
  (input  logic din,
   output logic dout);
  (* my_attribute = P_STR *)
  assign dout = din;
endmodule
module real_under_mod
  #(parameter real R1 = 1_23.45_67,
    parameter real R2 = 3.14_15e1_0)
  (input  real a,
   output real y);
  assign y = a + R1 + R2;
endmodule
module long_id_mod
  (input  logic clk,
   output logic q);
  logic [0:0]
    signal_name_that_is_definitely_longer_than_sixty_four_characters_and_should_trigger_internal_hashing_mechanism_of_verilator;
  assign signal_name_that_is_definitely_longer_than_sixty_four_characters_and_should_trigger_internal_hashing_mechanism_of_verilator = clk;
  assign q = signal_name_that_is_definitely_longer_than_sixty_four_characters_and_should_trigger_internal_hashing_mechanism_of_verilator;
endmodule
module wildcard_mod
  #(parameter string WILD = "*abc?d*")
  (input  logic [15:0] in_data,
   output logic [15:0] out_data);
  assign out_data = in_data;
endmodule
module whitespace_mod
  #(parameter string WS1 = "   \n\t  ",
    parameter string WS2 = "Word1   Word2")
  (input  logic i,
   output logic o);
  assign o = i;
endmodule
module mixed_feature_mod
  #(parameter string MIX_STR = "Before%%After\n\t\x55\125\012",
    parameter real  MIX_REAL = 9_87.65_43)
  (input  logic [7:0] data_in,
   output logic [7:0] data_out);
  (* combined_attr = MIX_STR *)
  logic [7:0] internal_signal_with_a_very_very_long_name_to_force_name_processing_mechanics_in_verilator;
  assign internal_signal_with_a_very_very_long_name_to_force_name_processing_mechanics_in_verilator = data_in;
  assign data_out = internal_signal_with_a_very_very_long_name_to_force_name_processing_mechanics_in_verilator + 8'(MIX_REAL);
endmodule
