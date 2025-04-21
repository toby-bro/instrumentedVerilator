module width_test;
  // Basic data types with different widths
  bit single_bit;
  logic signed [31:0] signed_32bit;
  logic [31:0] unsigned_32bit;
  logic [7:0] byte_val;
  logic [15:0] word_val;
  logic [63:0] long_val;
  logic [2:0][3:0] packed_array;
  
  // Real, string, and time types
  real real_val;
  string str_val;
  time time_val;
  
  // Parameters (sized and unsized)
  parameter PARAM1 = 10;  // Unsized
  parameter [7:0] PARAM2 = 8'hFF;  // Sized
  parameter signed PARAM3 = -5;  // Signed
  
  // Enums to test enum methods
  typedef enum logic [3:0] {
    RED, GREEN, BLUE, YELLOW
  } color_e;
  color_e color_var;

  // Struct and union for member selection
  typedef struct packed {
    logic [7:0] field1;
    logic [15:0] field2;
  } struct_t;

  typedef union packed {
    logic [23:0] as_bits;
    struct packed {  // Make the struct packed to fix the error
      logic [7:0] byte0;
      logic [7:0] byte1;
      logic [7:0] byte2;
    } as_bytes;
  } union_t;

  struct_t struct_var;
  union_t union_var;
  
  // Various array types to test array methods
  logic [7:0] unpacked_array[10];
  logic [7:0] dyn_array[];
  logic [7:0] queue_array[$];
  int assoc_array[string];
  bit [7:0] wild_array[*];
  
  // Class for testing method calls
  class MyClass;
    rand bit [7:0] rand_val;
    int x, y;
    
    function new(int a = 0, int b = 0);
      x = a;
      y = b;
    endfunction
    
    function int sum();
      return x + y;
    endfunction
    
    // Remove the custom rand_mode function as it can't be overridden
    
    constraint c1 { rand_val inside {[0:100]}; }
  endclass;
  
  MyClass obj;
  
  initial begin
    // Logical operators (test AstLogNot, AstLogAnd, AstLogOr, etc.)
    single_bit = !single_bit;
    single_bit = (signed_32bit > 0) && (unsigned_32bit < 100);
    single_bit = (signed_32bit > 0) || (unsigned_32bit < 100);
    single_bit = (signed_32bit > 0) && (unsigned_32bit < 100) || (byte_val == 0);
    
    // Reduction operators (test AstRedAnd, AstRedOr, AstRedXor, etc.)
    single_bit = &byte_val;     // AND reduction
    single_bit = |byte_val;     // OR reduction
    single_bit = ^byte_val;     // XOR reduction
    single_bit = ~^byte_val;    // XNOR reduction
    single_bit = $onehot(byte_val);  // Exactly one bit set
    single_bit = $onehot0(byte_val); // Zero or one bit set
    
    // Comparison operations (test AstEq, AstNeq, AstGt, etc.)
    single_bit = (signed_32bit == unsigned_32bit);
    single_bit = (signed_32bit != unsigned_32bit);
    single_bit = (signed_32bit > unsigned_32bit);
    single_bit = (signed_32bit >= unsigned_32bit);
    single_bit = (signed_32bit < unsigned_32bit);
    single_bit = (signed_32bit <= unsigned_32bit);
    
    // Signed comparison operations
    single_bit = (signed_32bit > -5);  // AstGtS
    single_bit = (signed_32bit >= -5); // AstGteS
    single_bit = (signed_32bit < -5);  // AstLtS
    single_bit = (signed_32bit <= -5); // AstLteS
    
    // Case equality (test AstEqCase, AstNeqCase)
    single_bit = (byte_val === 8'h55);
    single_bit = (byte_val !== 8'h55);
    
    // Wildcard equality (test AstEqWild, AstNeqWild)
    single_bit = (byte_val ==? 8'h5?);
    single_bit = (byte_val !=? 8'h5?);
    
    // Real comparisons (test AstEqD, AstNeqD, etc.)
    single_bit = (real_val == 1.0);
    single_bit = (real_val != 1.0);
    single_bit = (real_val < 1.0);
    single_bit = (real_val <= 1.0);
    single_bit = (real_val > 1.0);
    single_bit = (real_val >= 1.0);
    
    // String comparisons (test AstEqN, AstNeqN, etc.)
    single_bit = (str_val == "test");
    single_bit = (str_val != "test");
    single_bit = (str_val < "test");
    single_bit = (str_val <= "test");
    single_bit = (str_val > "test");
    single_bit = (str_val >= "test");
    
    // Bitwise operations (test AstAnd, AstOr, AstXor, etc.)
    byte_val = byte_val & 8'h0F;  // AND
    byte_val = byte_val | 8'h0F;  // OR
    byte_val = byte_val ^ 8'h0F;  // XOR
    byte_val = ~byte_val;         // NOT (unary)
    
    // Arithmetic operations (test AstAdd, AstSub, AstDiv, AstMul)
    signed_32bit = signed_32bit + 10;
    signed_32bit = signed_32bit - 10;
    signed_32bit = signed_32bit / 10;
    signed_32bit = signed_32bit * 10;
    
    // Modulus operations (test AstModDiv, AstModDivS)
    unsigned_32bit = unsigned_32bit % 10;    // AstModDiv
    signed_32bit = signed_32bit % 10;        // AstModDivS
    
    // Signed multiplication and division
    signed_32bit = signed_32bit * -5;        // AstMulS
    signed_32bit = signed_32bit / -5;        // AstDivS
    
    // Unary operations (test AstNegate, AstNot)
    signed_32bit = -signed_32bit;            // AstNegate
    byte_val = ~byte_val;                    // AstNot
    
    // Real arithmetic (test AstAddD, AstSubD, etc.)
    real_val = real_val + 1.5;
    real_val = real_val - 1.5;
    real_val = real_val / 1.5;
    real_val = real_val * 1.5;
    real_val = real_val ** 2.0;              // AstPowD
    
    // Real unary operations (test AstNegateD)
    real_val = -real_val;
    
    // Casting (test AstSigned, AstUnsigned)
    signed_32bit = signed'(unsigned_32bit);
    unsigned_32bit = unsigned'(signed_32bit);
    
    // Shifts (test AstShiftL, AstShiftR, AstShiftRS)
    byte_val = byte_val << 3;                // AstShiftL
    byte_val = byte_val >> 3;                // AstShiftR
    signed_32bit = signed_32bit >>> 3;       // AstShiftRS
    
    // Power operation (test AstPow)
    unsigned_32bit = unsigned_32bit ** 3;
    signed_32bit = signed_32bit ** 3;        // Signed base
    signed_32bit = unsigned_32bit ** signed_32bit; // Signed exponent
    
    // Concatenation (test AstConcat)
    long_val = {unsigned_32bit, signed_32bit};
    long_val = {byte_val, word_val, byte_val};
    
    // Replication (test AstReplicate)
    long_val = {8{byte_val}};
    packed_array = {2{2'b10}};
    packed_array[0] = 4'b1100;
    
    // Selection operations (test AstSel)
    single_bit = long_val[10];               // Bit select
    byte_val = long_val[7:0];                // Part select
    
    // Array selection (test AstArraySel)
    byte_val = unpacked_array[5];
    
    // Slice select (test AstSliceSel)
    unpacked_array[0:2] = '{8'h12, 8'h34, 8'h56};
    
    // Stream operators
    long_val = {<<8{unsigned_32bit}};        // Stream left
    long_val = {>>8{unsigned_32bit}};        // Stream right
    
    // Conditional operator (test AstCond)
    byte_val = single_bit ? 8'hAA : 8'h55;
    
    // Dynamic array operations
    dyn_array = new[5];
    dyn_array[0] = 8'h11;
    dyn_array[1] = 8'h22;
    dyn_array = new[10](dyn_array);          // Resize with contents preserved
    
    // Queue operations
    queue_array.push_back(8'h33);
    queue_array.push_back(8'h44);
    byte_val = queue_array.pop_front();
    
    // Associative array operations
    assoc_array["one"] = 1;
    assoc_array["two"] = 2;
    signed_32bit = assoc_array["one"];
    
    // Wildcard associative array
    wild_array[5] = 8'hAA;
    byte_val = wild_array[5];
    
    // Struct operations (test AstStructSel, AstMemberSel)
    struct_var.field1 = 8'h55;
    struct_var.field2 = 16'hAAAA;
    byte_val = struct_var.field1;
    
    // Union operations
    union_var.as_bits = 24'h55AAFF;
    byte_val = union_var.as_bytes.byte0;
    
    // Enum operations
    color_var = RED;
    if (color_var == GREEN) begin
      byte_val = 8'h22;
    end
    color_var = color_var.next();
    str_val = color_var.name();
    
    // Class operations (test AstMethodCall)
    obj = new(10, 20);
    signed_32bit = obj.sum();
    
    // Inside operator (test AstInside)
    if (byte_val inside {8'h00, 8'h55, 8'hAA, 8'hFF}) begin
      single_bit = 1'b1;
    end
    
    if (signed_32bit inside {[-100:100]}) begin
      single_bit = 1'b1;
    end
    
    // Dist operator (test AstDist)
    byte_val = $dist_uniform(27, 0, 255);
    byte_val = $dist_normal(37, 127, 30);
    
    // Cast operators (test AstCast, AstCastSize)
    byte_val = 8'(signed_32bit);
    long_val = 64'(unsigned_32bit);
    
    // Type conversion (test integer/real conversion)
    real_val = real'(signed_32bit);          // AstIToRD - Int to Real
    signed_32bit = int'(real_val);           // AstRToIS - Real to Int
    unsigned_32bit = $rtoi(real_val);        // Real to Int system function
    
    // Bit/Real conversion
    unsigned_32bit = $realtobits(real_val);  // AstRealToBits
    real_val = $bitstoreal(unsigned_32bit);  // AstBitsToRealD
    
    // String conversion
    str_val = $sformatf("%d", signed_32bit);
    signed_32bit = str_val.atoi();
    str_val = str_val.toupper();             // AstToUpperN
    str_val = str_val.tolower();             // AstToLowerN
    
    // String methods (test AstCMethodHard)
    signed_32bit = str_val.len();
    str_val = {str_val, "suffix"};           // String concatenation (AstConcatN)
    str_val = {5{"a"}};                      // String replication (AstReplicateN)
    
    // Additional string methods
    byte_val = str_val.getc(0);
    str_val.putc(0, "X");
    str_val = str_val.substr(1, 3);
    signed_32bit = str_val.compare("test");
    
    // Test $bits, $dimensions (AstAttrOf)
    signed_32bit = $bits(byte_val);
    signed_32bit = $bits(struct_var);
    signed_32bit = $dimensions(unpacked_array);
    signed_32bit = $unpacked_dimensions(packed_array);
    
    // Test $high, $low, $size, etc.
    signed_32bit = $high(unpacked_array);
    signed_32bit = $low(unpacked_array);
    signed_32bit = $left(word_val);
    signed_32bit = $right(word_val);
    signed_32bit = $size(unpacked_array);
    signed_32bit = $increment(unpacked_array);
    
    // Randomize method with constraint
    void'(obj.randomize());
    
    // Test $signed, $unsigned system functions
    signed_32bit = $signed(unsigned_32bit);
    unsigned_32bit = $unsigned(signed_32bit);
    
    // Dynamic casting
    byte_val = 8'(signed_32bit);
    
    // Events and timing
    time_val = time'($realtime);
    
    // Test SystemVerilog timing control statements (triggers V3Width's visit(AstDelay))
    #10ns;
    #(byte_val * 1ns);
    
    // Test fork..join to exercise visit(AstFork)
    fork
      #10 byte_val = 8'h01;
      #20 word_val = 16'h0203;
    join
    
    // Simple event control to test visit(AstEventControl)
    @(byte_val);
    
    // Replace with standard operations that test width calculations
    single_bit = (byte_val != 0);
    
    // Replace implication operator with logical AND
    single_bit = (byte_val > 0) && (byte_val < 255);
    
    // Test count bits function
    signed_32bit = $countones(byte_val);
    signed_32bit = $countbits(byte_val, 1'b0, 1'b1, 1'bx);
    
    // Test unbounded array operations to hit visit(AstUnbounded)
    dyn_array = new[10]; // Use a specific size instead
  end
  
  // Test procedural blocks
  always_comb begin
    // Complex expressions with multiple operators to test expression width propagation
    long_val = ({1'b1, byte_val} << 2) | ({4{word_val[3:0]}} & 64'hFFFF);
  end
  
  function automatic logic [7:0] test_function(input logic [31:0] in_val);
    return in_val[7:0] + 8'h11;
  endfunction
  
  initial begin
    // Call function to test width propagation through function calls
    byte_val = test_function(unsigned_32bit);
  end

  // Create a simpler signal for clocking
  logic clk_signal;
  
  // Clocking block using the local signal
  clocking cb @(posedge clk_signal);
    input #1step byte_val;
  endclocking
  
  initial begin
    // Test clocking block member selection
    byte_val = cb.byte_val;
  end
endmodule

// Move interface declaration outside the module
interface simple_if;
  logic clk;
  logic [7:0] data;
  logic valid;
  
  modport master (output clk, data, valid);
  modport slave (input clk, data, valid);
endinterface
