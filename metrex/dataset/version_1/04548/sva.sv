// SVA for carry_select_adder
// Bindable checker; uses clockless @(*) sampling for combinational DUT

module csa_sva (
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic [31:0] sum,
  // internal nets
  input  logic [31:0] c1, c2, p1, p2, g1, g2,
  input  logic [31:0] s1, s2, s3
);

  default clocking cb @(*); endclocking
  default disable iff ($isunknown({a,b,sum,c1,c2,p1,p2,g1,g2,s1,s2,s3}));

  // Functional correctness
  assert property (sum == a + b);

  // Internal computations equivalence
  assert property (s1 == a + b);
  assert property (s2 == (s1 - {c1,p1}));
  assert property (s3 == (s1 - {c2,p2}));

  // Expected structure of helper nets from assigns
  assert property (g2 == 32'd0);
  assert property (p2 == 32'd0);
  assert property (c2 == 32'd0);
  assert property (g1 == {30'd0, b[31], a[31]});
  assert property (p1 == {30'd0, ~b[31], ~a[31]});
  assert property (c1 == {29'd0, b[31], a[31], 1'b0});

  // Selection behavior (first branch is unreachable due to g2==0)
  assert property ((g1 & g2) == 32'd0);
  assert property ((a[31] | b[31])  -> (sum == s2));
  assert property ((!(a[31] | b[31])) -> (sum == s1));
  assert property (s3 == s1); // since {c2,p2} == 0

  // Coverage: exercise both result paths and overflow cases
  cover property (!(a[31] | b[31]) && sum == s1);
  cover property ( (a[31] | b[31]) && sum == s2);
  cover property ((a + b) < a);           // unsigned overflow
  cover property ((a == 32'd0) && (b == 32'd0));
  cover property ((a == 32'hFFFF_FFFF) && (b == 32'd1));

endmodule

// Bind to all instances of the adder (accesses internal nets)
bind carry_select_adder csa_sva u_csa_sva (
  .a(a), .b(b), .sum(sum),
  .c1(c1), .c2(c2), .p1(p1), .p2(p2), .g1(g1), .g2(g2),
  .s1(s1), .s2(s2), .s3(s3)
);