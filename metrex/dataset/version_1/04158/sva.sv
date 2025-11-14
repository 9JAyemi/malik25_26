// SVA for full_adder and top_module
// Focused, high-quality checks with concise coverage

// Assertions bound into each full_adder bit instance
module full_adder_sva (
  input a,
  input b,
  input cin,
  input sum,
  input cout
);
  // Functional correctness
  assert property (@(*)) sum == (a ^ b ^ cin)
    else $error("full_adder.sum mismatch");

  assert property (@(*)) cout == ((a & b) | (a & cin) | (b & cin))
    else $error("full_adder.cout mismatch");

  // No X/Z on any pin
  assert property (@(*)) !$isunknown({a,b,cin,sum,cout})
    else $error("full_adder has X/Z");

  // Minimal input-combination coverage (all 8 combos)
  genvar k;
  for (k = 0; k < 8; k++) begin : CMB
    localparam [2:0] pat = k[2:0];
    cover property (@(*)) {a,b,cin} == pat;
  end
endmodule

bind full_adder full_adder_sva fa_sva (.*);

// Assertions bound into top_module
module top_module_sva (
  input         clk,
  input  [31:0] a,
  input  [31:0] b,
  input         sub,
  input  [31:0] sum,

  // Internal signals of top_module (connected by bind .*)
  input  [31:0] a_reg,
  input  [31:0] b_reg,
  input  [31:0] a_xor_b,
  input  [31:0] sub_xor_sum,
  input  [31:0] sub_and_b,
  input  [31:0] sub_and_sum,
  input  [31:0] sub_and_cin,
  input  [31:0] cin
);
  default clocking @(posedge clk); endclocking

  // Upstream inputs known
  assert property (!$isunknown({a,b,sub})) else $error("Inputs X/Z");

  // Registered capture
  assert property (a_reg == $past(a)) else $error("a_reg != past(a)");
  assert property (b_reg == $past(b)) else $error("b_reg != past(b)");

  // Internal combinational definitions
  assert property (a_xor_b   == (a_reg ^ b_reg))  else $error("a_xor_b mismatch");
  assert property (cin       == {32{sub}})        else $error("cin mismatch");
  assert property (sub_and_b == ({32{sub}} & b_reg)) else $error("sub_and_b mismatch");
  assert property (sub_and_sum==({32{sub}} & sum))   else $error("sub_and_sum mismatch");
  assert property (sub_and_cin==(sub_and_b | sub_and_sum)) else $error("sub_and_cin mismatch");
  assert property (sub_xor_sum == (sum ^ sub)) else $error("sub_xor_sum mismatch");

  // Array-of-full-adders sum behavior (3-input XOR per bit)
  assert property (sum == (a_xor_b ^ sub_and_cin ^ cin))
    else $error("Top sum mismatch vs FA inputs");

  // No X/Z on critical nets (helps catch algebraic loop issues)
  assert property (!$isunknown({a_reg,b_reg,sum,a_xor_b,sub_and_b,sub_and_sum,sub_and_cin,cin}))
    else $error("Internal X/Z detected");

  // Detect/forbid unsolvable feedback condition per bit: sub=1, a=0, b=0
  genvar i;
  for (i=0; i<32; i++) begin : ILLEGAL
    assert property (!(sub && !a_reg[i] && !b_reg[i]))
      else $error("Illegal combo causes algebraic loop: sub=1 a_reg[%0d]=0 b_reg[%0d]=0", i, i);
  end

  // Minimal functional coverage
  // Mode coverage
  cover property (sub == 0 && sum == (a_reg ^ b_reg));
  cover property (sub == 1);

  // Per-bit coverage that the FA path is exercised in both modes
  for (i=0; i<32; i++) begin : COV
    cover property (sub==0 && sum[i] == a_xor_b[i]);
    cover property (sub==1 && b_reg[i]==1 && sum[i] == a_xor_b[i]);
  end
endmodule

bind top_module top_module_sva top_sva (.*);