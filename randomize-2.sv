module GGG_RandVars_Mod (input logic GGGin, output logic GGGout);
  logic GGG_local_logic;

  class GGG_RandClassBasic;
    rand int GGG_my_int;
    randc bit [15:0] GGG_my_shortint;
    rand logic GGG_my_logic;
    //INJECT

    function new();
      //INJECT
    endfunction

    function int randomize();
      // Basic randomize call triggers C++ processing
      //INJECT
      return 1;
    endfunction
  endclass

  assign GGGout = GGGin; // Placeholder to use output
  //INJECT

  // Example usage context (will be analyzed by Verilator)
  always @(posedge GGGin) begin
    GGG_RandClassBasic GGG_inst = new();
    // The class definition and rand/randc keywords trigger the C++ logic.
    // A simulation randomize() call would also trigger it, but is not needed for AST analysis.
    // GGG_inst.randomize();
    GGG_local_logic = GGG_inst.GGG_my_logic; // Use a member to keep it
    //INJECT
  end

endmodule

module GGG_SimpleConstraint_Mod (input logic GGGin, output logic GGGout);
  logic GGGout;

  class GGG_ConstrClass;
    rand int GGG_val1;
    rand int GGG_val2;
    //INJECT

    constraint GGG_sum_constraint {
      GGG_val1 + GGG_val2 == 100; //INJECT
      GGG_val1 > 0;
      GGG_val2 < 101;
    }

    function new();
      //INJECT
    endfunction

    function int randomize();
      //INJECT
      return 1;
    endfunction
  endclass

  assign GGGout = GGGin;
  //INJECT

  always @(posedge GGGin) begin
    GGG_ConstrClass GGG_inst = new();
    // The constraint definition and rand keywords trigger the C++ logic.
    // GGG_inst.randomize();
    //INJECT
    $cast(GGG_inst, null); // Dummy operation
  end

endmodule

module GGG_RandomizeWith_Mod (input logic GGGin, output logic GGGout);
  logic GGGout;

  class GGG_RandWithClass;
    rand int GGG_x;
    rand int GGG_y;
    //INJECT

    constraint GGG_base_constraint {
      GGG_x < 50; //INJECT
    }

    function new();
      //INJECT
    endfunction

    function int randomize();
      // The C++ handles randomize() calls and transforms 'with'
      // The presence of the class definition and constraints is key.
      //INJECT
      return 1;
    endfunction
  endclass

  assign GGGout = GGGin;
  //INJECT

  always @(posedge GGGin) begin
    GGG_RandWithClass GGG_inst = new();
    // The 'with' clause is processed at the call site or via analysis of the class definition.
    // The class itself is sufficient to trigger some processing.
    // Example of randomize with (triggers C++ 'with' handling) - Keep commented for linting
    // if (GGGin) begin
    //   GGG_inst.randomize() with { GGG_y > GGG_x; GGG_y < 100; }; // Simulation/fuzzing context
    // end
    //INJECT
    $cast(GGG_inst, null); // Dummy operation
  end

endmodule

module GGG_RandModeConstrMode_Mod (input logic GGGin, output logic GGGout);
  logic GGGout;

  class GGG_ModeControlClass;
    rand int GGG_data1;
    rand int GGG_data2;
    //INJECT

    constraint GGG_range_constr {
      GGG_data1 inside {[1:10]}; //INJECT
      GGG_data2 inside {[90:100]};
    }

    function new();
      //INJECT
    endfunction

    function int randomize();
      //INJECT
      return 1;
    endfunction

    task GGG_set_modes(input bit GGG_rand_on, input bit GGG_constr_on);
      // Calls to rand_mode and constraint_mode trigger C++ handling
      // Keep commented out to avoid potential elaboration issues without full class context
      // this.GGG_data1.rand_mode(GGG_rand_on); //INJECT
      // this.GGG_range_constr.constraint_mode(GGG_constr_on); //INJECT
      // GGG_data2.rand_mode(GGG_rand_on); // Implicit 'this' - triggers C++
      //INJECT
    endtask
  endclass

  assign GGGout = GGGin;
  //INJECT

  always @(posedge GGGin) begin
    GGG_ModeControlClass GGG_inst = new();
    // The calls to rand_mode/constraint_mode trigger the C++ logic.
    // The method definition is sufficient for AST analysis.
    // GGG_inst.GGG_set_modes(GGGin, !GGGin); // Simulation context
    //INJECT
    $cast(GGG_inst, null); // Dummy operation
  end

endmodule

module GGG_Randcase_Mod (input logic GGGin, output logic GGGout);
  logic GGGout;
  int GGG_selection;
  logic GGG_action_taken;

  always @(posedge GGGin) begin
    GGG_action_taken = 0; //INJECT
    randcase // Correct syntax: no expression in parentheses after randcase keyword
      10 : begin GGG_selection = 1; GGG_action_taken = 1; end // Weights are the expressions
      20 : begin GGG_selection = 2; GGG_action_taken = 1; end
      30 : begin GGG_selection = 3; GGG_action_taken = 1; end
      //INJECT
    endcase
    //INJECT
  end

  assign GGGout = GGG_action_taken; // Use internal variable for output
  //INJECT

endmodule

module GGG_ArrayRandom_Mod (input logic GGGin, output logic GGGout);
  logic GGGout;

  class GGG_ArrayClass;
    rand int GGG_unpacked_array [0:7]; // Unpacked array
    rand int GGG_dynamic_array [];    // Dynamic array
    rand int GGG_queue [$];           // Queue
    rand int GGG_assoc_array [string]; // Associative array
    //INJECT

    constraint GGG_array_constr {
      // Note: .size constraint on unpacked array is not standard,
      // but Verilator might handle it for analysis purposes.
      // Standard is just declaring the unpacked array size.
      // GGG_unpacked_array.size == 8; // Size constraint on unpacked array (often implicit)
      GGG_dynamic_array.size inside {[2:5]}; // Size constraint on dynamic array
      //INJECT
      foreach (GGG_unpacked_array[GGG_i]) GGG_unpacked_array[GGG_i] inside {[1:10]}; // Foreach
      foreach (GGG_dynamic_array[GGG_j]) GGG_dynamic_array[GGG_j] > 0; // Foreach
      GGG_queue.size() < 10; // size() method
      //INJECT
    }

    function new();
      // Dynamic array needs allocation before use
      GGG_dynamic_array = new[0]; // Needs a size later randomized by constraints
      //INJECT
    endfunction

    function int randomize();
      //INJECT
      return 1;
    endfunction
  endclass

  assign GGGout = GGGin;
  //INJECT

  always @(posedge GGGin) begin
    GGG_ArrayClass GGG_inst = new();
    // Array types and constraints trigger C++ processing.
    // GGG_inst.randomize();
    // Access elements/methods to ensure they are processed
    if (GGGin) begin
       int GGG_temp = GGG_inst.GGG_unpacked_array[0]; //INJECT
       int GGG_temp_size_da = GGG_inst.GGG_dynamic_array.size(); // Size method usage - triggers C++ processing
       int GGG_temp_size_q = GGG_inst.GGG_queue.size(); // Size method usage - triggers C++ processing
       // GGG_inst.GGG_assoc_array["key"] = 1; // Assoc array usage - access triggers some processing
    end
  end

endmodule

module GGG_StructUnionEnumRand_Mod (input logic GGGin, output logic GGGout);
  logic GGGout;

  typedef enum {GGG_RED, GGG_GREEN, GGG_BLUE} GGG_Color_e;

  typedef struct packed {
    logic GGG_en;
    bit [7:0] GGG_data;
  } GGG_PackedStruct_s;

  typedef struct { // Unpacked struct
    int GGG_id;
    GGG_Color_e GGG_status;
  } GGG_UnpackedStruct_s;

  typedef union packed {
    bit [15:0] GGG_word;
    bit [7:0] GGG_bytes [2];
  } GGG_PackedUnion_u;

  // Unpacked union is unsupported for rand/randc

  class GGG_ComplexTypeClass;
    rand GGG_Color_e GGG_color_val;
    rand GGG_PackedStruct_s GGG_packed_struct;
    rand GGG_UnpackedStruct_s GGG_unpacked_struct; // Unpacked struct can be randomized
    rand GGG_PackedUnion_u GGG_packed_union;
    //INJECT

    constraint GGG_complex_constr {
      GGG_color_val != GGG_BLUE; //INJECT
      GGG_packed_struct.GGG_en == 1; // Access packed struct member
      GGG_unpacked_struct.GGG_id > 0; // Access unpacked struct member
      //INJECT
      GGG_packed_union.GGG_bytes[0] inside {[0:127]}; // Access packed union array member
    }

    function new();
      //INJECT
    endfunction

    function int randomize();
      //INJECT
      return 1;
    endfunction
  endclass

  assign GGGout = GGGin;
  //INJECT

  always @(posedge GGGin) begin
    GGG_ComplexTypeClass GGG_inst = new();
    // Structure types and constraints trigger C++ processing.
    // GGG_inst.randomize();
    // Access members to ensure processing
    if (GGGin) begin
      GGG_Color_e GGG_temp_color = GGG_inst.GGG_color_val; //INJECT
      GGG_PackedStruct_s GGG_temp_ps = GGG_inst.GGG_packed_struct;
      GGG_UnpackedStruct_s GGG_temp_ups = GGG_inst.GGG_unpacked_struct;
      GGG_PackedUnion_u GGG_temp_pu = GGG_inst.GGG_packed_union;
    end
  end

endmodule

module GGG_ConstraintBuiltins_Mod (input logic GGGin, output logic GGGout);
  logic GGGout;

  class GGG_BuiltinConstrClass;
    rand int GGG_my_array []; // Dynamic array
    rand int GGG_value;
    //INJECT

    constraint GGG_builtin_constr {
      GGG_my_array.size() inside {[5:10]}; // size() method - triggers C++ processing
      GGG_value inside {GGG_my_array};    // inside {array} - triggers C++ processing
      //INJECT
      // inside {range} and inside {list} covered in previous modules
      // size() method also covered
    }

    function new();
      GGG_my_array = new[0]; // Allocate dynamic array (size randomized by constraint)
      //INJECT
    endfunction

    function int randomize();
      //INJECT
      return 1;
    endfunction
  endclass

  assign GGGout = GGGin;
  //INJECT

  always @(posedge GGGin) begin
    GGG_BuiltinConstrClass GGG_inst = new();
    // Builtin constraint methods trigger C++ processing.
    // GGG_inst.randomize();
    // Use members/methods
    if (GGGin) begin
      int GGG_s = GGG_inst.GGG_my_array.size(); //INJECT
      int GGG_v = GGG_inst.GGG_value;
    end
  end

endmodule

module GGG_ClassInheritance_Mod (input logic GGGin, output logic GGGout);
  logic GGGout;

  class GGG_BaseClass;
    rand int GGG_base_var;
    //INJECT

    constraint GGG_base_constr {
      GGG_base_var > 0; //INJECT
    }

    function new();
      //INJECT
    endfunction

    virtual function int randomize();
      //INJECT
      return 1;
    endfunction

    // Demonstrate pre/post randomize
    task pre_randomize();
      //INJECT
    endtask

    task post_randomize();
      //INJECT
    endtask
  endclass

  class GGG_DerivedClass extends GGG_BaseClass;
    rand int GGG_derived_var;
    //INJECT

    constraint GGG_derived_constr {
      GGG_derived_var > GGG_base_var; //INJECT
      GGG_derived_var < 100;
      //INJECT
    }

    function new();
      super.new();
      //INJECT
    endfunction

    virtual function int randomize();
      //INJECT
      return super.randomize();
    endfunction

    // Override pre/post randomize
    task pre_randomize();
      super.pre_randomize();
      //INJECT
    endtask

    task post_randomize();
      super.post_randomize();
      //INJECT
    endtask
  endclass

  assign GGGout = GGGin;
  //INJECT

  always @(posedge GGGin) begin
    GGG_DerivedClass GGG_inst = new();
    // Inheritance, virtual methods, super calls, pre/post randomize trigger C++ processing.
    // GGG_inst.randomize();
    // GGG_BaseClass GGG_base_inst;
    // $cast(GGG_base_inst, GGG_inst); // Cast might trigger some C++ processing
    // if (GGG_base_inst) GGG_base_inst.randomize(); // Call on base class ref
    //INJECT
    if (GGGin) begin
      int GGG_temp = GGG_inst.GGG_derived_var;
    end
  end

endmodule

module GGG_StaticMember_Mod (input logic GGGin, output logic GGGout);
  logic GGGout;

  class GGG_StaticClass;
    static rand int GGG_static_rand; // Static rand member
    //INJECT

    constraint GGG_static_constr {
      GGG_static_rand < 1000; // Static constraint
      //INJECT
    }

    function new();
      //INJECT
    endfunction

    // Static members can be randomized
    static function int randomize();
      // Static randomize method - triggers C++ processing
      //INJECT
      return 1;
    endfunction

    // Unsupported: rand_mode on static variable (as noted in C++ code comment)
    // task GGG_control_static_mode(input bit on);
    //   GGG_static_rand.rand_mode(on); // This is the unsupported call site to trigger analysis
    // endtask
  endclass

  assign GGGout = GGGin;
  //INJECT

  always @(posedge GGGin) begin
    // Access static member to trigger its processing
    if (GGGin) begin
      int GGG_temp = GGG_StaticClass::GGG_static_rand; //INJECT
      // GGG_StaticClass::randomize(); // Static method call - triggers C++ processing
    end
  end

endmodule
