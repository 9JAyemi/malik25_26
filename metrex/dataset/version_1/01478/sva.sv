// SVA for top_module and adder16bit
// Focused, concise checks + key coverage. Purely combinational, sampled @(*).

// Bind into top_module
module top_module_sva;
  default clocking cb @(*); endclocking
  default disable iff ($isunknown({a,b,select}));

  // Basic structural splits
  assert property (a_low == a[15:0]) else $error("a_low split mismatch");
  assert property (b_low == b[15:0]) else $error("b_low split mismatch");

  // Carry-in decode
  assert property (carry_in == (select ? ~b[15] : 1'b0)) else $error("carry_in decode mismatch");
  assert property (!select |-> (carry_in == 1'b0)) else $error("carry_in should be 0 when select==0");
  assert property ( select |-> (carry_in == ~b[15])) else $error("carry_in should be ~b[15] when select==1");

  // 16-bit adder output (as used in top)
  assert property (sum_low == (a_low + b_low + carry_in)[15:0]) else $error("sum_low mismatch");

  // Check the instantiated adder is hooked up as expected
  assert property (adder.a === a_low) else $error("adder.a port not wired to a_low");
  assert property (adder.b === b_low) else $error("adder.b port not wired to b_low");
  assert property (adder.carry_in === carry_in) else $error("adder.carry_in port not wired to carry_in");
  assert property (adder.sum === sum_low) else $error("adder.sum port not wired to sum_low");

  // Sum path functional checks per select
  assert property (!select |-> (sum == ({sum_low, a[31:16]} + {a_low, b_low})[31:0]))
    else $error("sum mismatch in select==0 path");

  assert property ( select |-> (sum == ({~b,1'b1} + a)[31:0]))
    else $error("sum mismatch in select==1 path");

  // Output should not be X/Z when inputs are known
  assert property (!$isunknown(sum)) else $error("sum has X/Z");

  // Key coverage
  // Exercise both select paths
  cover property (!select);
  cover property ( select);

  // In select==1 path, cover both b[15] polarities (affects carry_in)
  cover property (select && (b[15] == 1'b0)); // carry_in == 1
  cover property (select && (b[15] == 1'b1)); // carry_in == 0

  // In select==0 path, cover no-carry and carry out of the 16-bit low adder
  // (derive carry-out from 17-bit recompute)
  cover property (!select && (({1'b0,a_low}+{1'b0,b_low}+carry_in)[16] == 1'b0));
  cover property (!select && (({1'b0,a_low}+{1'b0,b_low}+carry_in)[16] == 1'b1));
endmodule

bind top_module top_module_sva tmsva();

// Bind into adder16bit
module adder16bit_sva;
  default clocking cb @(*); endclocking
  default disable iff ($isunknown({a,b,carry_in}));

  // Functional correctness (lower 16 bits)
  assert property (sum == (a + b + carry_in)[15:0]) else $error("adder16bit sum mismatch");

  // Cover adder carry-out both 0/1
  cover property ((({1'b0,a}+{1'b0,b}+carry_in)[16]) == 1'b0);
  cover property ((({1'b0,a}+{1'b0,b}+carry_in)[16]) == 1'b1);
endmodule

bind adder16bit adder16bit_sva a16sva();