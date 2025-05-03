module top (
  input logic GGGin,
  output logic GGGout
);

  assign GGGout = GGGin; //INJECT

endmodule

module GGG_ClassRandMembers (
  input logic GGGin,
  output logic [7:0] GGGout
);

  class GGG_MyRandClass;
    rand bit GGG_rand_bit; //INJECT
    rand byte GGG_rand_byte; //INJECT
    rand int GGG_rand_int; //INJECT
    randc logic [15:0] GGG_randc_logic; //INJECT
    rand bit [3:0] GGG_rand_vector; //INJECT

    function new();
      //INJECT
    endfunction
  endclass

  // The presence of the class definition with rand/randc members is sufficient
  // to exercise the C++ code paths that identify randomizable variables.

  assign GGGout = {8{GGGin}}; // Dummy assignment //INJECT

endmodule

module GGG_ClassRandHooks ( // Renamed to reflect presence of pre/post hooks
  input logic GGGin,
  output logic GGGout
);

  class GGG_ClassWithRandHooks;
    rand int GGG_rand_var; //INJECT

    // The 'randomize' method is built-in and cannot be explicitly declared.
    // V3Randomize.cpp likely handles parsing the *use* of randomize()
    // and the definition of pre/post_randomize and rand/randc members.

    task GGG_pre_randomize(); //INJECT
      // Placeholder for pre-randomize logic
      // This task CAN be declared by the user
      //INJECT
      if (GGGin) begin
        // Example logic
        GGG_rand_var = 0; // Resetting before randomization
      end
      //INJECT
    endtask

    task GGG_post_randomize(); //INJECT
      // Placeholder for post-randomize logic
      // This task CAN be declared by the user
      //INJECT
      if (GGGin) begin
        // Example logic
        // $display("Post-randomize called: GGG_rand_var = %0d", GGG_rand_var); // Avoid simulation tasks
      end
      //INJECT
    endtask

    function new(); //INJECT
      //INJECT
    endfunction
  endclass

  assign GGGout = GGGin; // Dummy assignment //INJECT

endmodule

module GGG_ClassConstraints (
  input logic GGGin,
  output logic GGGout
);

  class GGG_ClassWithConstraints;
    rand int GGG_a; //INJECT
    rand int GGG_b; //INJECT
    rand int GGG_c []; // Dynamic array //INJECT
    rand bit [7:0] GGG_d [5]; // Fixed-size unpacked array //INJECT
    rand logic GGG_e; //INJECT

    constraint GGG_simple_constr { //INJECT
      GGG_a > 0; //INJECT
      GGG_b < 100; //INJECT
      GGG_e == GGGin; // Constraint based on module input //INJECT
    }

    constraint GGG_complex_constr { //INJECT
      // Constraints involving dynamic array size and methods
      // Ensure GGG_c is sized before randomization
      if (GGG_c.size() > 0) (GGG_a + GGG_b) == GGG_c.size(); // Constraint involving size of dynamic array //INJECT
      GGG_d.sum() with (int'(item)) inside {[10:50]}; // foreach and sum on fixed array //INJECT
      unique { GGG_a, GGG_b }; // unique constraint //INJECT
      GGG_d.min() > 5; // min method //INJECT
      //INJECT
    }

    constraint GGG_solve_before_constr { // This constraint type is handled by V3Randomize
      solve GGG_a before GGG_b; //INJECT
      GGG_b > GGG_a; //INJECT
    }

    function new(); //INJECT
      //INJECT
      GGG_c = new[5]; // Initialize dynamic array size for randomization //INJECT
      // INJECT // Potential injection point after array initialization
    endfunction
  endclass

  assign GGGout = GGGin; // Dummy assignment //INJECT

endmodule

module GGG_ClassRandMode (
  input logic GGGin,
  output logic GGGout
);

  class GGG_ClassWithRandMode;
    rand int GGG_member_a; //INJECT
    rand logic GGG_member_b; //INJECT
    rand bit [3:0] GGG_member_c [2]; //INJECT

    task GGG_setup_rand_modes(); //INJECT
      // Placeholder to show context where rand_mode calls might exist
      // The C++ code handles parsing calls like object.rand_mode(..) or variable.rand_mode(..)
      // The presence of the member names is sufficient for fuzzing targets.
      // this.GGG_member_a.rand_mode(0); // Illustrative context for member rand_mode //INJECT
      // this.GGG_member_b.rand_mode(1); // Illustrative context //INJECT
      // this.GGG_member_c.rand_mode(1); // Illustrative context for array member //INJECT
      // this.rand_mode(0); // Illustrative context for object rand_mode //INJECT
      //INJECT
    endtask

    function new(); //INJECT
      //INJECT
    endfunction
  endclass

  assign GGGout = GGGin; // Dummy assignment //INJECT

endmodule

module GGG_ClassConstraintMode (
  input logic GGGin,
  output logic GGGout
);

  class GGG_ClassWithConstraintMode;
    rand int GGG_value; //INJECT
    rand int GGG_other_value; //INJECT

    constraint GGG_con1 { GGG_value inside {[1:10]}; } //INJECT
    constraint GGG_con2 { GGG_value > 5; } //INJECT
    constraint GGG_con3 { (GGG_value + GGG_other_value) < 20; } //INJECT

    task GGG_setup_constraint_modes(); //INJECT
      // Placeholder to show context where constraint_mode calls might exist
      // this.GGG_con1.constraint_mode(0); // Illustrative context for constraint_mode //INJECT
      // this.GGG_con2.constraint_mode(1); // Illustrative context //INJECT
      // this.constraint_mode(0); // Illustrative context for object constraint_mode //INJECT
      //INJECT
    endtask

    function new(); //INJECT
      //INJECT
    endfunction
  endclass

  assign GGGout = GGGin; // Dummy assignment //INJECT

endmodule

module GGG_ModuleRandcase (
  input logic GGGin,
  output logic [1:0] GGGout
);

  logic [1:0] GGG_result; //INJECT
  int GGG_weight1 = 1; // Randcase weights must be positive integers or expressions evaluating to positive integers //INJECT
  int GGG_weight2 = 2; //INJECT
  int GGG_weight_in = GGGin ? 3 : 1; // Example: weight based on input, ensure > 0 when used //INJECT

  always_comb begin
    // Use the actual randcase keyword to exercise the corresponding AST node in V3Randomize.cpp
    // Selects one branch based on weighted probability
    randcase //INJECT
      // Use constant weights for simplicity, or variables guaranteed > 0
      1         : GGG_result = 2'b01; // Weight 1 //INJECT
      2         : GGG_result = 2'b10; // Weight 2 //INJECT
      GGG_weight_in : GGG_result = 2'b11; // Weight based on GGG_weight_in, ensured > 0 //INJECT
      //INJECT // Potential injection point inside randcase items
    endcase //INJECT
  end

  assign GGGout = GGG_result; //INJECT

endmodule

module GGG_ClassComplexTypesRand (
  input logic GGGin,
  output logic GGGout
);

  typedef enum { GGG_STATE_IDLE, GGG_STATE_ACTIVE, GGG_STATE_DONE } GGG_enum_t; //INJECT

  typedef struct packed {
    logic [3:0] GGG_sub_field_a; //INJECT
    logic [7:0] GGG_sub_field_b; //INJECT
  } GGG_packed_struct_t; //INJECT

  // Structs are unpacked by default unless 'packed' is specified.
  typedef struct {
    int GGG_unpacked_field_a; //INJECT
    byte GGG_unpacked_field_b; //INJECT
  } GGG_unpacked_struct_t; //INJECT

  class GGG_ComplexRandClass;
    rand int GGG_basic_int; //INJECT
    rand GGG_enum_t GGG_enum_var; //INJECT
    rand GGG_packed_struct_t GGG_packed_struct_var; //INJECT
    rand GGG_unpacked_struct_t GGG_unpacked_struct_var; //INJECT
    rand logic [3:0] GGG_packed_array [2]; // Packed array //INJECT
    rand int GGG_unpacked_array [3]; // Unpacked array //INJECT
    rand byte GGG_dynamic_array []; // Dynamic array //INJECT
    rand string GGG_associative_array [*]; // Associative array //INJECT
    rand real GGG_queue [$]; // Queue //INJECT
    rand bit GGG_bit; //INJECT
    rand GGG_ComplexRandClass GGG_nested_obj; // Rand handle? Verilator might simplify this. //INJECT

    constraint GGG_complex_types_constr { //INJECT
      GGG_enum_var != GGG_STATE_DONE; // Constraint on enum //INJECT
      GGG_packed_struct_var.GGG_sub_field_a inside {[0:8]}; // Constraint on packed struct field //INJECT
      GGG_unpacked_struct_var.GGG_unpacked_field_a > 10; // Constraint on unpacked struct field //INJECT
      GGG_packed_array.sum() < 30; // Constraint on packed array //INJECT
      GGG_unpacked_array.min() > -5; // Constraint on unpacked array //INJECT
      GGG_dynamic_array.size() inside {[1:10]}; // Constraint on dynamic array size //INJECT
      // Associative arrays and queues cannot typically be directly constrained on elements unless iterated.
      // GGG_nested_obj is a handle, constraints on it might be complex.
      //INJECT
    }

    function new(); //INJECT
      //INJECT
      // Initialize dynamic array and queue size for randomization
      GGG_dynamic_array = new[4]; //INJECT
      GGG_queue = new[2]; // Initialize queue size //INJECT
      // INJECT // Potential injection point after array/queue initialization
    endfunction

    // The 'randomize' method is built-in and cannot be explicitly declared.
    // V3Randomize.cpp handles processing rand/randc members and constraints.
  endclass

  assign GGGout = GGGin; // Dummy assignment //INJECT

endmodule

module GGG_ModuleRandsequence (
  input logic GGGin,
  output logic GGGout
);

  // This module exercises the randsequence construct, which is part of
  // the randomization features handled by V3Randomize.cpp.

  logic GGG_local_var; //INJECT

  // randsequence can appear in tasks or functions. Place in a dummy task.
  task GGG_run_randsequence(); //INJECT
    // Example randsequence structure
    // The grammar and rules are processed by Verilator's front-end
    randsequence (GGG_local_var) //INJECT
      GGG_rule1 : { GGG_local_var = 1; next GGG_rule2; } | { GGG_local_var = 0; }; //INJECT
      GGG_rule2 : { GGG_local_var = GGGin; }; //INJECT
      //INJECT // Potential injection point for more rules
    endsequence //INJECT
  endtask

  assign GGGout = GGGin & GGG_local_var; // Dummy assignment using local var //INJECT

endmodule
