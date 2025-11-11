// SVA bind module for adder_4bit_with_cin
module adder_4bit_with_cin_sva (
  input logic [3:0] a,
  input logic [3:0] b,
  input logic       cin,
  input logic [3:0] out,
  input logic       cout
);
  default clocking cb @($global_clock); endclocking

  // Reference ripple carries
  logic c1, c2, c3;
  assign c1 = (a[0] & b[0]) | ((a[0] ^ b[0]) & cin);
  assign c2 = (a[1] & b[1]) | ((a[1] ^ b[1]) & c1);
  assign c3 = (a[2] & b[2]) | ((a[2] ^ b[2]) & c2);

  // X-prop safety
  a_no_x: assert property (!$isunknown({a,b,cin}) |-> ##0 !$isunknown({out,cout}));

  // End-to-end correctness (golden model)
  a_sum_ok: assert property (!$isunknown({a,b,cin}) |-> ##0 ({cout,out} == (a + b + cin)));

  // Bitwise correctness (pinpoint stage failures)
  a_b0:   assert property (!$isunknown({a,b,cin}) |-> ##0 (out[0] == (a[0] ^ b[0] ^ cin)));
  a_b1:   assert property (!$isunknown({a,b,cin}) |-> ##0 (out[1] == (a[1] ^ b[1] ^ c1)));
  a_b2:   assert property (!$isunknown({a,b,cin}) |-> ##0 (out[2] == (a[2] ^ b[2] ^ c2)));
  a_b3:   assert property (!$isunknown({a,b,cin}) |-> ##0 (out[3] == (a[3] ^ b[3] ^ c3)));
  a_cout: assert property (!$isunknown({a,b,cin}) |-> ##0 (cout    == ((a[3] & b[3]) | ((a[3] ^ b[3]) & c3))));

  // Sanity equivalences
  a_cout_match_sum: assert property (!$isunknown({a,b,cin}) |-> ##0 (cout == ((a + b + cin) > 4'hF)));
  a_out_lowbits:    assert property (!$isunknown({a,b,cin}) |-> ##0 (out  == (a + b + cin)[3:0]));

  // Functional coverage
  c_no_ovf:         cover property (!$isunknown({a,b,cin}) && ((a + b + cin) < 16));
  c_ovf:            cover property (!$isunknown({a,b,cin}) && ((a + b + cin) >= 16));
  c_zero:           cover property (!$isunknown({a,b,cin}) && (a==4'h0) && (b==4'h0) && !cin);
  c_full_prop:      cover property (!$isunknown({a,b,cin}) && ((a ^ b) == 4'hF) && cin);      // full propagate chain
  c_gen_msb:        cover property (!$isunknown({a,b,cin}) && (a[3] & b[3]));                  // MSB generate
  c_max_inputs:     cover property (!$isunknown({a,b,cin}) && (a==4'hF) && (b==4'hF) && cin);  // worst-case overflow
endmodule

bind adder_4bit_with_cin adder_4bit_with_cin_sva (
  .a(a), .b(b), .cin(cin), .out(out), .cout(cout)
);