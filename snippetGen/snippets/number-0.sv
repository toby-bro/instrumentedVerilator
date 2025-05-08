// Numeric Literal Parsing Module
module LiteralParsing(
  input logic [7:0] in_byte,
  output logic [15:0] out_sized_hex,
  output logic [15:0] out_unsized_dec,
  output logic out_unbased_x,
  output logic out_unbased_z,
  output logic out_unbased_0,
  output logic out_unbased_1,
  output real out_real
);

  assign out_sized_hex = 16'hDEAD; // Sized hex
  assign out_unsized_dec = 'd12345; 
  assign out_unbased_x = 'x;     // Unbased x
  assign out_unbased_z = 'z;     // Unbased z
  assign out_unbased_0 = '0;     // Unbased 0 (1-bit value 0)
  assign out_unbased_1 = '1;     // Unbased 1 (1-bit value 1)
  assign out_real = 3.14159;      // Real literal

  always_comb begin
    //INJECT
    logic [3:0] temp_bits = 4'b101x;
    //INJECT
    logic [7:0] combined = {temp_bits, in_byte[3:0]};
    out_sized_hex = {in_byte[7:4], combined};
    //INJECT
  end

endmodule

// Basic Logic Assignments with 4-State
module LogicAssignments(
  input logic [3:0] in_val,
  output logic [7:0] out_assign,
  output logic [7:0] out_x,
  output logic [7:0] out_z
);

  logic [7:0] temp_reg;

  assign out_x = 8'hx; // All X
  assign out_z = 8'hz; // All Z

  always_comb begin
    //INJECT
    temp_reg = {4'b1010, in_val};
    //INJECT
    out_assign = temp_reg;
  end

endmodule

// Real and String Assignments
module RealStringAssignments(
  input real in_real,
  input string in_str,
  output real out_real,
  output string out_str
);

  real temp_real;
  string temp_str;

  always_comb begin
    //INJECT
    temp_real = in_real * 2.0;
    //INJECT
    temp_str = in_str.toupper();
    out_real = temp_real;
    out_str = temp_str;
    //INJECT
  end

endmodule

// Bitwise Operations
module BitwiseOps(
  input logic [7:0] in_a,
  input logic [7:0] in_b,
  output logic [7:0] out_not_a,
  output logic [7:0] out_and,
  output logic [7:0] out_or,
  output logic [7:0] out_xor
);

  assign out_not_a = ~in_a;
  assign out_and = in_a & in_b;
  assign out_or = in_a | in_b;
  assign out_xor = in_a ^ in_b;

  always_latch begin
    //INJECT
    logic [7:0] temp = out_and | out_xor;
    //INJECT
    if (|temp) out_not_a = ~out_not_a; // Example logic using temp
  end

endmodule

// Reduction Operations
module ReductionOps(
  input logic [15:0] in_vec,
  output logic out_red_and,
  output logic out_red_or,
  output logic out_red_xor,
  output logic out_red_nand,
  output logic out_red_nor,
  output logic out_red_nxor
);

  assign out_red_and = &in_vec;
  assign out_red_or = |in_vec;
  assign out_red_xor = ^in_vec;
  assign out_red_nand = ~&in_vec;
  assign out_red_nor = ~|in_vec;
  assign out_red_nxor = ~^in_vec;

  always_latch begin
    //INJECT
    logic temp = out_red_and && out_red_or;
    //INJECT
    if (temp) out_red_xor = ~out_red_xor;
  end

endmodule

// Logical Operations
module LogicalOps(
  input logic in_a,
  input logic in_b,
  output logic out_log_not_a,
  output logic out_log_and,
  output logic out_log_or
);

  assign out_log_not_a = !in_a;
  assign out_log_and = in_a && in_b;
  assign out_log_or = in_a || in_b;

  always_latch begin
    //INJECT
    logic temp = out_log_and || out_log_or;
    //INJECT
    if (temp) out_log_not_a = !out_log_not_a;
  end

endmodule

// Arithmetic Operations (Unsigned)
module ArithmeticOps(
  input logic [7:0] in_a,
  input logic [7:0] in_b,
  output logic [7:0] out_add,
  output logic [7:0] out_sub,
  output logic [7:0] out_mul,
  output logic [7:0] out_div,
  output logic [7:0] out_mod,
  output logic [15:0] out_pow
);

  assign out_add = in_a + in_b;
  assign out_sub = in_a - in_b;
  assign out_mul = in_a * in_b;
  assign out_div = (in_b == 0) ? 'x : in_a / in_b; // Avoid division by zero
  assign out_mod = (in_b == 0) ? 'x : in_a % in_b; // Avoid modulus by zero
  assign out_pow = in_a ** in_b; // Power operator

  always_comb begin
    //INJECT
    logic [7:0] temp_add = out_add + 1;
    //INJECT
    out_sub = temp_add - in_b;
  end

endmodule

// Signed Arithmetic Operations
module SignedArithmeticOps(
  input int in_a,
  input int in_b,
  output int out_add,
  output int out_sub,
  output int out_mul,
  output int out_div,
  output int out_mod
);

  assign out_add = in_a + in_b;
  assign out_sub = in_a - in_b;
  assign out_mul = in_a * in_b;
  assign out_div = (in_b == 0) ? 'x : in_a / in_b; // Avoid division by zero
  assign out_mod = (in_b == 0) ? 'x : in_a % in_b; // Avoid modulus by zero

  always_comb begin
    //INJECT
    int temp_mul = out_mul * 2;
    //INJECT
    // Division by a constant can be tricky with X/Z.
    // For simplicity, let's ensure the divisor is non-zero or handle the X case.
    // If temp_mul is 'x', division result is also 'x'. Integer division by 4
    out_div = temp_mul / 4;
  end

endmodule

// Comparison Operations (Unsigned and 4-State)
module ComparisonOps(
  input logic [7:0] in_a,
  input logic [7:0] in_b,
  output logic out_eq,
  output logic out_neq,
  output logic out_gt,
  output logic out_lt,
  output logic out_gte,
  output logic out_lte,
  output logic out_case_eq,
  output logic out_case_neq
);

  assign out_eq = (in_a == in_b);
  assign out_neq = (in_a != in_b);
  assign out_gt = (in_a > in_b);
  assign out_lt = (in_a < in_b);
  assign out_gte = (in_a >= in_b);
  assign out_lte = (in_a <= in_b);
  assign out_case_eq = (in_a === in_b);
  assign out_case_neq = (in_a !== in_b);

  always_latch begin
    //INJECT
    logic temp = out_eq || out_neq;
    //INJECT
    if (temp) out_gt = ~out_gt;
  end

endmodule

// Signed Comparison Operations
module SignedComparisonOps(
  input int in_a,
  input int in_b,
  output logic out_eq,
  output logic out_neq,
  output logic out_gt,
  output logic out_lt,
  output logic out_gte,
  output logic out_lte
);

  assign out_eq = (in_a == in_b);
  assign out_neq = (in_a != in_b);
  assign out_gt = (in_a > in_b);
  assign out_lt = (in_a < in_b);
  assign out_gte = (in_a >= in_b);
  assign out_lte = (in_a <= in_b);

  always_latch begin
    //INJECT
    logic temp = out_gt && out_lt;
    //INJECT
    if (temp) out_gte = ~out_gte;
  end

endmodule


// Shift Operations
module ShiftOps(
  input logic [7:0] in_a,
  input int in_shift,
  output logic [7:0] out_sll,
  output logic [7:0] out_srl,
  output logic [7:0] out_sra
);

  assign out_sll = in_a << in_shift; // Logical left shift
  assign out_srl = in_a >> in_shift; // Logical right shift
  assign out_sra = $signed(in_a) >>> in_shift; // Arithmetic right shift

  always_comb begin
    //INJECT
    logic [7:0] temp = out_sll | out_srl;
    //INJECT
    out_sra = temp >>> 1;
  end

endmodule

// Concatenation and Replication
module ConcatRepl(
  input logic [3:0] in_a,
  input logic [4:0] in_b,
  input int in_repl_count, // in_repl_count is not used in assign/always, but kept as input
  output logic [8:0] out_concat,
  output logic [7:0] out_repl // Changed replication size to be fixed for simplicity
);

  parameter REPL_COUNT = 2;

  assign out_concat = {in_b, in_a}; // Concatenation
  assign out_repl = {REPL_COUNT {in_a[0]}}; // Replication

  always_comb begin
    //INJECT
    logic [1:0] temp_part = in_a[1:0];
    //INJECT
    out_concat = {in_b[4:2], temp_part, in_a[3:2]};
  end

endmodule

// Part Select
module PartSelect(
  input logic [15:0] in_vec,
  input int in_lsb,
  output logic [7:0] out_fixed_part,
  output logic [7:0] out_dyn_part
);

  assign out_fixed_part = in_vec[7:0]; // Fixed part-select
  // Ensure dynamic part-select access is valid within the vector bounds
  assign out_dyn_part = (in_lsb >= 0 && in_lsb + 8 <= 16) ? in_vec[in_lsb +: 8] : 'x; // Dynamic part-select with bounds check

  always_comb begin
    //INJECT
    logic [3:0] temp_slice = in_vec[11:8];
    //INJECT
    out_fixed_part = {temp_slice, in_vec[3:0]};
  end

endmodule

// Part Select Assignment
module PartSelectAssign(
  input logic [15:0] in_base,
  input logic [7:0] in_value,
  input int in_lsb,
  output logic [15:0] out_vec
);

  logic [15:0] temp_vec;

  always_comb begin
    temp_vec = in_base;
    //INJECT
    temp_vec[7:0] = in_value; // Fixed part-select assignment
    //INJECT
    // Ensure dynamic part-select access is valid within the vector bounds before assignment
    if (in_lsb >= 0 && in_lsb + 8 <= 16) begin
        temp_vec[in_lsb +: 8] = in_value; // Dynamic part-select assignment
    end else begin
        // Handle out-of-bounds case, maybe assign 'x to a part or the whole vector
        temp_vec = 'x; // Assign entire vector to x on invalid access attempt
    end
    out_vec = temp_vec;
  end

endmodule

// String Operations
module StringOps(
  input string in_str1,
  input string in_str2,
  input int in_index,
  output int out_len,
  output bit [7:0] out_char_at,
  output string out_substr,
  output int out_compare,
  output string out_tolower,
  output string out_toupper,
  output string out_concat,
  output string out_repl
);

  parameter REPL_COUNT = 2;

  assign out_len = in_str1.len();
  assign out_char_at = (in_index >= 0 && in_index < in_str1.len()) ? in_str1[in_index] : 8'h0; // String indexing (getc) with bounds check
  assign out_substr = in_str1.substr(0, (in_str1.len() > 0 ? in_str1.len() - 1 : 0)); // Substring (handle empty string)
  assign out_compare = in_str1.compare(in_str2);
  assign out_tolower = in_str1.tolower();
  assign out_toupper = in_str1.toupper();
  assign out_concat = in_str1 + in_str2; // String concatenation
  // String replication {count {string}} is not standard SystemVerilog. Use concatenation loop if needed.
  // Assigning an empty string for now as direct replication is not supported like bit vectors.
  // A more robust approach for string replication requires a loop/task/function.
  // Let's simulate a simple fixed replication for fuzzer exercise.
  assign out_repl = in_str1 + in_str1; // Simulate replication for REPL_COUNT=2

  always_comb begin
    string temp_str = in_str1;
    //INJECT
    // String indexing (putc) with bounds check
    if (in_index >= 0 && in_index < temp_str.len()) begin
      temp_str[in_index] = 8'h41; // 'A'
    end
    //INJECT
    // Dynamic substring with bounds check
    if (in_index >= 0 && in_index + 1 <= temp_str.len()) begin
       out_substr = temp_str.substr(in_index, in_index + 1);
    end else begin
       out_substr = ""; // Assign empty string if out of bounds
    end
  end

endmodule

// Real Operations
module RealOps(
  input real in_a,
  input real in_b,
  output real out_add,
  output real out_sub,
  output real out_mul,
  output real out_div,
  output real out_pow,
  output logic out_eq,
  output logic out_neq,
  output logic out_gt,
  output logic out_lt
);

  assign out_add = in_a + in_b;
  assign out_sub = in_a - in_b;
  assign out_mul = in_a * in_b;
  assign out_div = (in_b == 0.0) ? 1.0e38 : in_a / in_b; // Avoid division by zero
  assign out_pow = in_a ** in_b; // Power operator

  assign out_eq = (in_a == in_b);
  assign out_neq = (in_a != in_b);
  assign out_gt = (in_a > in_b);
  assign out_lt = (in_a < in_b);

  always_comb begin
    //INJECT
    real temp_mul = out_mul * 3.0;
    //INJECT
    out_div = temp_mul / 5.0;
  end

endmodule

// Type Conversions (Integer/Logic <-> Real, Real <-> Bits)
module TypeConversions(
  input logic [31:0] in_int,
  input real in_real,
  input logic [63:0] in_real_bits,
  output real out_itor,
  output int out_rtoi,
  output int out_rtoiround, // Renamed to avoid implying rounding logic if $round is unavailable
  output logic [63:0] out_realtobits,
  output real out_bitstoreal
);

  assign out_itor = $itor(in_int); // Integer to real
  assign out_rtoi = $rtoi(in_real); // Real to integer (truncates)
  assign out_rtoiround = $rtoi(in_real); // Real to integer (truncates)
  assign out_realtobits = $realtobits(in_real); // Real to IEEE 754 bits
  assign out_bitstoreal = $bitstoreal(in_real_bits); // IEEE 754 bits to real

  always_comb begin
    //INJECT
    real temp_real = $itor(in_int + 1);
    //INJECT
    out_itor = temp_real;
  end

endmodule

// System Functions like $clog2, $onehot, $onehot0
module SystemFunctions(
  input int in_int,
  input logic [7:0] in_vec,
  output int out_clog2,
  output logic out_onehot,
  output logic out_onehot0,
  output int out_countones
);

  assign out_clog2 = (in_int > 0) ? $clog2(in_int) : 0; // Ceiling log base 2
  assign out_onehot = $onehot(in_vec); // Checks if exactly one bit is 1
  assign out_onehot0 = $onehot0(in_vec); // Checks if at most one bit is 1
  assign out_countones = $countones(in_vec); // Counts set bits

  always_comb begin
    //INJECT
    logic temp_oh = $onehot({~in_vec});
    //INJECT
    out_onehot = out_onehot || temp_oh;
  end

endmodule

// Using x/z in operations (exercising opBits*, isAnyXZ, etc.)
module FourStateOps(
  input logic [7:0] in_a,
  input logic [7:0] in_b,
  output logic [7:0] out_and_xz,
  output logic out_any_xz_a,
  output logic [7:0] out_bits_non_x_a,
  output logic [7:0] out_bits_z_a
);

  assign out_and_xz = in_a & in_b; // Test logic AND with X/Z inputs
  assign out_any_xz_a = |(in_a ^ in_a); // Should detect X/Z bits (X^X=X, Z^Z=X, then |X=X)

  // Simulate some of the opBits* functionality with custom logic
  always_comb begin
    logic [7:0] temp_vec; // Declare temp_vec here

    out_bits_non_x_a = 8'b0;
    out_bits_z_a = 8'b0;
    for(int i=0; i<8; i++) begin
      if (in_a[i] !== 1'bx && in_a[i] !== 1'bz) begin
        out_bits_non_x_a[i] = 1;
      end
      if (in_a[i] === 1'bz) begin
        out_bits_z_a[i] = 1;
      end
    end
    //INJECT
    temp_vec = in_a | out_bits_non_x_a; // Assign temp_vec after declaration
    //INJECT
    out_and_xz = temp_vec & in_b;
  end

endmodule

// Use of parameters in number contexts
module ParameterizedWidth #(parameter int WIDTH = 16) (
  input logic [WIDTH-1:0] in_val,
  output logic [WIDTH-1:0] out_shifted
);

  assign out_shifted = in_val << 1;

  always_comb begin
    //INJECT
    logic [WIDTH-1:0] temp = in_val >> 2;
    //INJECT
    out_shifted = temp | in_val;
  end

endmodule

// Example of logic that might involve checking MSB for signedness
module SignedCheckExample(
  input logic [7:0] in_val,
  output logic out_is_negative
);

  // Simple check if MSB is 1 (for assumed 2's complement signed)
  assign out_is_negative = in_val[7];

  always_comb begin
    //INJECT
    logic [7:0] temp = in_val + 8'd1;
    //INJECT
    out_is_negative = temp[7];
  end

endmodule
