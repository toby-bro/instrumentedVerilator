module BasicRandClass(
    input bit clk,
    output int int_t_out,
    output int int_rc_out,
    output int enum_t_out
);
  typedef enum { RED, GREEN, BLUE, YELLOW } color_e;
  class MyBasicRandClass;
    rand int rand_int_var;
    randc int randc_int_var;
    rand color_e rand_enum_var;
    function new();
      rand_int_var = 0;
      randc_int_var = 0;
      rand_enum_var = RED;
    endfunction
    function void pre_randomize();
    endfunction
    function void post_randomize();
    endfunction
    function void set_seed(int seed);
    endfunction
  endclass
  MyBasicRandClass inst_basic_rand_class;
  always_comb begin
    if (inst_basic_rand_class == null) begin
      inst_basic_rand_class = new();
    end
    void'(inst_basic_rand_class.randomize());
    int_t_out = inst_basic_rand_class.rand_int_var;
    int_rc_out = inst_basic_rand_class.randc_int_var;
    enum_t_out = inst_basic_rand_class.rand_enum_var;
  end
endmodule
module RandModeControl(
    input bit enable_rand_var,
    input bit enable_all_constraints,
    output int rand_var_out,
    output int constr_var_out
);
  class MyRandModeClass;
    rand int my_rand_var;
    rand int my_other_rand_var;
    static rand int static_rand_var;
    constraint c1 { my_rand_var > 10; }
    constraint c2 { my_other_rand_var < 100; }
    static constraint static_c {
      static_rand_var > 0;
    }
    function new();
      my_rand_var = 0;
      my_other_rand_var = 0;
      static_rand_var = 0;
    endfunction
  endclass
  MyRandModeClass inst_rand_mode_class;
  always_comb begin
    if (inst_rand_mode_class == null) begin
      inst_rand_mode_class = new();
    end
    if (enable_rand_var) begin
      void'(inst_rand_mode_class.my_rand_var.rand_mode(1));
    end else begin
      void'(inst_rand_mode_class.my_rand_var.rand_mode(0));
    end
    if (enable_all_constraints) begin
      void'(inst_rand_mode_class.c1.constraint_mode(1));
    end else begin
      void'(inst_rand_mode_class.c1.constraint_mode(0));
    end
    if (enable_rand_var && enable_all_constraints) begin
      void'(inst_rand_mode_class.rand_mode(1));
    end else begin
      void'(inst_rand_mode_class.rand_mode(0));
    end
    if (enable_all_constraints && enable_rand_var) begin
      void'(inst_rand_mode_class.constraint_mode(1));
    end else begin
      void'(inst_rand_mode_class.constraint_mode(0));
    end
    void'(MyRandModeClass::static_c.constraint_mode(1));
    void'(MyRandModeClass::static_rand_var.rand_mode(1));
    void'(inst_rand_mode_class.randomize());
    rand_var_out = inst_rand_mode_class.my_rand_var;
    constr_var_out = inst_rand_mode_class.my_other_rand_var;
  end
endmodule
module ComplexConstraints(
    input bit [7:0] in_seed,
    output int val_a_out,
    output int val_b_out,
    output int val_c_out
);
  class MyComplexConstrainedClass;
    rand int a;
    rand int b;
    rand int c;
    rand int dyn_array[];
    rand int queue_var[$];
    rand int assoc_array[int];
    constraint complex_c {
      a > 0 && a < 100;
      b == a + 1;
      c != b * 2;
      (a % 2 == 0) -> (b % 2 == 1);
      !(c > 50);
      a inside { [10:20], 5, 90 };
      $countones(b) == 3;
      b[7:0] == 8'hFF;
      {8{a[0]}} == 8'b0;
      dyn_array.size() inside { [5:10] };
      foreach (dyn_array[i]) {
        dyn_array[i] inside { [0:100] };
        dyn_array[i] == i;
      }
      queue_var.size() == 3;
      foreach (queue_var[idx]) {
        queue_var[idx] < 50;
      }
      assoc_array.num() == 2;
      foreach (assoc_array[key]) {
        assoc_array[key] > 10;
        if (key == 1) assoc_array[key] == 15;
        else assoc_array[key] == 25;
      }
    }
    constraint solve_order_c {
      solve a before b;
      b == a + 1;
    }
    constraint unique_c {
      unique {dyn_array};
    }
    function new();
      a = 0; b = 0; c = 0;
      dyn_array = new[0];
      queue_var = {};
    endfunction
  endclass
  MyComplexConstrainedClass inst_complex_constrained_class;
  always_comb begin
    if (inst_complex_constrained_class == null) begin
      inst_complex_constrained_class = new();
    end
    void'(inst_complex_constrained_class.randomize());
    val_a_out = inst_complex_constrained_class.a;
    val_b_out = inst_complex_constrained_class.b;
    val_c_out = inst_complex_constrained_class.c;
  end
endmodule
module StructuredTypesRandomization(
    input bit [1:0] selector,
    output int val_packed_out,
    output int val_unpacked_out,
    output int val_union_out
);
  typedef struct packed {
    logic [7:0] field1;
    logic [7:0] field2;
  } packed_struct_t;
  typedef struct {
    int field_a;
    int field_b;
  } unpacked_struct_t;
  typedef union packed {
    int u_int;
    logic [31:0] u_short;
  } packed_union_t;
  class MyStructuredClass;
    rand packed_struct_t packed_s;
    rand unpacked_struct_t unpacked_s;
    rand packed_union_t packed_u;
    rand unpacked_struct_t dyn_struct_array[];
    rand unpacked_struct_t assoc_struct_array[string];
    constraint s_constr {
      packed_s.field1 > 10;
      packed_s.field2 < 50;
      unpacked_s.field_a == unpacked_s.field_b;
      packed_u.u_int inside { [1:100] };
      dyn_struct_array.size() == 2;
      foreach (dyn_struct_array[i]) {
        dyn_struct_array[i].field_a inside { [10:20] };
      }
      assoc_struct_array.num() == 1;
      foreach (assoc_struct_array[k]) {
        assoc_struct_array[k].field_b == 123;
      }
    }
    function new();
      packed_s.field1 = 0; packed_s.field2 = 0;
      unpacked_s.field_a = 0; unpacked_s.field_b = 0;
      packed_u.u_int = 0;
      dyn_struct_array = new[0];
    endfunction
  endclass
  MyStructuredClass inst_structured_class;
  always_comb begin
    if (inst_structured_class == null) begin
      inst_structured_class = new();
    end
    void'(inst_structured_class.randomize());
    val_packed_out = inst_structured_class.packed_s.field1;
    val_unpacked_out = inst_structured_class.unpacked_s.field_a;
    val_union_out = inst_structured_class.packed_u.u_int;
  end
endmodule
module InlineStdRandomize(
    input bit [7:0] in_data,
    output int val_a_out,
    output int val_b_out,
    output int module_level_rand_out
);
  logic module_level_rand_var;
  class MyInlineRandClass;
    rand int val_a;
    rand int val_b;
    rand int nested_struct_field;
    rand MyInlineRandClass nested_obj;
    typedef struct {
      int s_field1;
      int s_field2;
    } my_nested_struct_t;
    rand my_nested_struct_t nested_s;
    function new();
      val_a = 0; val_b = 0;
      nested_struct_field = 0;
      nested_s.s_field1 = 0;
      nested_s.s_field2 = 0;
      nested_obj = null;
    endfunction
  endclass
  MyInlineRandClass inst_inline_rand_class;
  always_comb begin
    if (inst_inline_rand_class == null) begin
      inst_inline_rand_class = new();
    end
    void'(inst_inline_rand_class.randomize() with {
      inst_inline_rand_class.val_a inside { [1:10] };
      inst_inline_rand_class.val_b == inst_inline_rand_class.val_a + 5;
      inst_inline_rand_class.nested_s.s_field1 > 0;
      inst_inline_rand_class.nested_s.s_field2 < 100;
    });
    void'(std::randomize(module_level_rand_var) with {
      module_level_rand_var > 100;
      module_level_rand_var < 200;
    });
    val_a_out = inst_inline_rand_class.val_a;
    val_b_out = inst_inline_rand_class.val_b;
    module_level_rand_out = module_level_rand_var;
  end
endmodule
module RandCaseStatement(
    input bit enable_randcase,
    output int chosen_value
);
  always_comb begin
    int rand_val;
    chosen_value = 0;
    if (enable_randcase) begin
      randcase
        10: begin rand_val = 1; end
        20: begin rand_val = 2; end
        0:  begin rand_val = 3; end
        30: begin rand_val = 4; end
      endcase
    end else begin
      rand_val = -1;
    end
    chosen_value = rand_val;
  end
endmodule
