// SVA checker for signed_mag_multiplier
// Bind this module to the DUT and drive clk/rst_n from your env.

module signed_mag_multiplier_sva (input logic clk, input logic rst_n);
  default clocking @(posedge clk); endclocking
  default disable iff (!rst_n)

  // The following names resolve into the bound DUT scope
  // DUT ports: a, b, product, overflow
  // DUT internals: temp_a, temp_b, temp_product, overflow_flag

  localparam signed MIN4 = -8;
  localparam signed MAX4 =  7;
  localparam signed MIN8 = -128;
  localparam signed MAX8 =  127;

  // No X/Z on outputs when inputs are known
  assert property ( !$isunknown({a,b}) |-> !$isunknown({product,overflow}) );

  // Sign predicate sanity
  assert property ( !$isunknown(a) |-> ((a < 0) == a[3]) );
  assert property ( !$isunknown(b) |-> ((b < 0) == b[3]) );

  // Functional correctness: 4x4 signed -> exact 8-bit signed product
  assert property ( $signed(product) == ($signed(a) * $signed(b)) );

  // Overflow must reflect true range violation (and for 4x4->8 it must never assert)
  assert property ( overflow == (($signed(a)*$signed(b) > MAX8) || ($signed(a)*$signed(b) < MIN8)) );
  assert property ( !overflow );

  // Internal abs() behavior (two's-complement negate)
  assert property ( (a >= 0) |-> (temp_a == a) );
  assert property ( (a  < 0) |-> (temp_a == -$signed(a)) );
  assert property ( (b >= 0) |-> (temp_b == b) );
  assert property ( (b  < 0) |-> (temp_b == -$signed(b)) );

  // Expected magnitude multiply path: temp_product non-negative unless a or b is MIN4
  assert property ( (a != MIN4 && b != MIN4) |-> (temp_product >= 0) );

  // Product sign rule when result non-zero
  assert property ( ($signed(a)*$signed(b) != 0) |-> (product[7] == (a[3] ^ b[3])) );

  // Targeted functional coverage
  cover property ( $signed(a)==0 && $signed(b)==0 && $signed(product)==0 );
  cover property ( a[3]==0 && b[3]==0 && $signed(product) >= 0 );
  cover property ( a[3]==1 && b[3]==1 && $signed(product) >= 0 );
  cover property ( a[3]^b[3] && $signed(product) <= 0 );
  cover property ( $signed(a)==MIN4 && $signed(b)==MIN4 && $signed(product)==64 );
  cover property ( $signed(a)==MIN4 && $signed(b)==1 );
  cover property ( $signed(a)==1    && $signed(b)==MIN4 );
  cover property ( $signed(a)==MAX4 && $signed(b)==MAX4 && $signed(product)==(MAX4*MAX4) );

endmodule

// Bind (connect clk/rst_n from your environment)
bind signed_mag_multiplier signed_mag_multiplier_sva u_signed_mag_multiplier_sva (.clk(clk), .rst_n(rst_n));