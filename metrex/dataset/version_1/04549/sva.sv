// SVA for adder_4bit_carry
// Bind into the DUT; focuses on correctness, X-safety, and key internal relations.
module adder_4bit_carry_sva;
  // Sample on any input change
  default clocking cb @(a or b or cin); endclocking

  // Helpers
  let add_ext = {1'b0, a} + {1'b0, b} + cin;
  let c0 = (a[0] & b[0]) | (cin & (a[0] ^ b[0]));
  let c1 = (a[1] & b[1]) | (c0 & (a[1] ^ b[1]));
  let c2 = (a[2] & b[2]) | (c1 & (a[2] ^ b[2]));
  let c3 = (a[3] & b[3]) | (c2 & (a[3] ^ b[3]));

  // X-safety: when inputs are known, outputs must be known
  a_no_x_out: assert property (!$isunknown({a,b,cin}) |-> !$isunknown({sum,cout}));

  // Golden functional check
  a_add_ok: assert property (!$isunknown({a,b,cin}) |-> {cout, sum} == add_ext);

  // Bit-level checks (granular debugging)
  a_sum0:   assert property (!$isunknown({a[0],b[0],cin}) |-> sum[0] == (a[0] ^ b[0] ^ cin));
  a_sum1:   assert property (!$isunknown({a[1],b[1]}) && !$isunknown(c0) |-> sum[1] == (a[1] ^ b[1] ^ c0));
  a_sum2:   assert property (!$isunknown({a[2],b[2]}) && !$isunknown(c1) |-> sum[2] == (a[2] ^ b[2] ^ c1));
  a_sum3:   assert property (!$isunknown({a[3],b[3]}) && !$isunknown(c2) |-> sum[3] == (a[3] ^ b[3] ^ c2));
  a_cout:   assert property (!$isunknown({a,b,cin}) |-> cout == c3);

  // Internal consistency with implementation intent
  a_half_sum_xor: assert property (!$isunknown({a,b}) |-> (half_sum == (a ^ b)));
  a_final_sum_rel: assert property (!$isunknown({half_sum,cin}) |-> sum == (half_sum ^ {3'b000, cin}));

  // Flag missing/undriven carry chain element
  a_full_sum0_driven: assert property (!$isunknown({a,b,cin}) |-> !$isunknown(full_sum[0]));

  // Coverage (key scenarios)
  c_nocarry:  cover property (!$isunknown({a,b,cin}) && (add_ext == 5'h00));
  c_overflow: cover property (!$isunknown({a,b,cin}) && add_ext[4]);
  c_ripple:   cover property (!$isunknown({a,b,cin}) && (a ^ b) == 4'hF && (a & b) == 4'h0 && cin && add_ext[4]);
  c_max:      cover property (!$isunknown({a,b,cin}) && (a == 4'hF) && (b == 4'hF) && !cin);

endmodule

bind adder_4bit_carry adder_4bit_carry_sva;