// SVA for four_bit_adder
// Bind once in your testbench: bind four_bit_adder four_bit_adder_sva sva();

module four_bit_adder_sva;
  default clocking cb @(*); endclocking

  // Golden computations
  wire [4:0] add5 = a + b + cin;
  wire [1:0] lo0 = a[0]     + b[0]     + cin;
  wire [2:0] lo1 = a[1:0]   + b[1:0]   + cin;
  wire [3:0] lo2 = a[2:0]   + b[2:0]   + cin;
  wire [4:0] lo3 = a[3:0]   + b[3:0]   + cin;
  wire       exp_c1 = lo0[1];
  wire       exp_c2 = lo1[2];
  wire       exp_c3 = lo2[3];
  wire       exp_c4 = lo3[4];
  wire [3:0] exp_sum = (a ^ b) ^ {exp_c3, exp_c2, exp_c1, cin};

  // Cleanliness
  assert property (!$isunknown({a,b,cin}) |-> !$isunknown({sum,cout,g,p,c}));

  // Top-level functional equivalence
  assert property ({cout,sum} == add5);

  // Internal PG correctness
  assert property (g == (a ^ b));
  assert property (p == (a & b));

  // Carry chain correctness
  assert property (c[0] == cin);
  assert property (c[1] == exp_c1);
  assert property (c[2] == exp_c2);
  assert property (c[3] == exp_c3);
  assert property (c[4] == exp_c4);

  // Sum/carry relations
  assert property (sum == exp_sum);
  assert property (cout == exp_c4);

  // Targeted coverage
  cover property ({cout,sum} == 5'h00);                 // 0 + 0 + 0
  cover property ({cout,sum} == 5'h10);                 // overflow to 16
  cover property (cin && ((a ^ b) == 4'hF) && cout);    // full propagate chain
  cover property (a[0] && b[0] && c[1]);
  cover property (a[1] && b[1] && c[2]);
  cover property (a[2] && b[2] && c[3]);
  cover property (a[3] && b[3] && c[4]);
endmodule

bind four_bit_adder four_bit_adder_sva sva();