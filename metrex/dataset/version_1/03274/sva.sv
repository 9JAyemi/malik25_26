// SVA for ripple_carry_adder, carry_save_adder, top_module
// Bind these checkers to the DUTs

// ---------------- ripple_carry_adder SVA ----------------
module rca_sva (
  input  [31:0] a,
  input  [31:0] b,
  input         cin,
  input  [31:0] sum,
  input         cout
);
  // Reference (matches DUT width rules)
  wire [31:0] exp_s = a ^ b ^ cin;
  wire [31:0] exp_c = (a & b) | (a & cin) | (b & cin);

  // Functional equivalence
  assert property (@(*) sum  == exp_s);
  assert property (@(*) cout == exp_c[31]);

  // No X/Z on outputs when inputs are known
  assert property (@(*) (!$isunknown({a,b,cin})) |-> (!$isunknown({sum,cout})));

  // Compact coverage
  cover property (@(*) cin==1'b0);
  cover property (@(*) cin==1'b1);
  cover property (@(*) (a[31] & b[31]) && cout);
  cover property (@(*) (a==32'h0000_0000 && b==32'h0000_0000 && !cin));
  cover property (@(*) (a==32'hFFFF_FFFF && b==32'hFFFF_FFFF &&  cin));
endmodule

bind ripple_carry_adder rca_sva rca_sva_i (.*);

// ---------------- carry_save_adder SVA ----------------
module csa_sva (
  input  [31:0] a,
  input  [31:0] b,
  input         cin,
  input  [31:0] sum,
  input         carry,
  // tap internals
  input  [31:0] s1,
  input         c1,
  input         c2
);
  wire [31:0] s1_ref  = a ^ b;
  wire        c1_ref  = a[31] & b[31];
  wire [31:0] sum_ref = s1_ref ^ {31'b0, cin} ^ {31'b0, c1_ref};

  // Check internal stage 1
  assert property (@(*) s1 == s1_ref);
  assert property (@(*) c1 == c1_ref);

  // Check final outputs
  assert property (@(*) sum   == sum_ref);
  assert property (@(*) carry == c2);
  // Due to DUT structure, this carry is always 0
  assert property (@(*) c2 == 1'b0);

  // No X/Z on outputs when inputs are known
  assert property (@(*) (!$isunknown({a,b,cin})) |-> (!$isunknown({sum,carry})));

  // Coverage of interesting interactions
  cover property (@(*) c1 && cin);                      // both MSB-carry-gen and cin set
  cover property (@(*) sum[0] != (a[0] ^ b[0]));        // LSB affected by carries
  cover property (@(*) (a[31] & b[31]));                // MSB carry generation in stage 1
endmodule

bind carry_save_adder csa_sva csa_sva_i (.*);

// ---------------- top_module SVA ----------------
module top_sva (
  input  [31:0] a,
  input  [31:0] b,
  input         sub,
  input  [31:0] sum,
  // tap internals
  input  [31:0] b_inverted,
  input         cin
);
  wire [31:0] binv_ref = sub ? ~b : b;
  wire        cin_ref  = sub;
  wire [31:0] sum_ref  = (a ^ binv_ref) ^ {31'b0, cin_ref} ^ {31'b0, (a[31] & binv_ref[31])};

  // Check pre-CSA transforms
  assert property (@(*) b_inverted == binv_ref);
  assert property (@(*) cin        == cin_ref);

  // End-to-end functional check vs. reference model of this DUT
  assert property (@(*) sum == sum_ref);

  // No X/Z on outputs when inputs are known
  assert property (@(*) (!$isunknown({a,b,sub})) |-> (!$isunknown(sum)));

  // Coverage: add vs sub and MSB interaction
  cover property (@(*) sub==1'b0);
  cover property (@(*) sub==1'b1);
  cover property (@(*) (a[31] & binv_ref[31]));
endmodule

bind top_module top_sva top_sva_i (.*);