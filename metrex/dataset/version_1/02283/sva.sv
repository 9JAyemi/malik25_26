// SVA for ripple_carry_adder, detect_carry_adder, and GDA_St_N8_M4_P2
// Focused, high-quality checks with concise coverage.

// -------------------------------------------
// ripple_carry_adder SVA
// -------------------------------------------
module ripple_carry_adder_sva (
  input logic [1:0] a,
  input logic [1:0] b,
  input logic       cin,
  input logic [1:0] sum,
  input logic       cout
);
  default clocking cb @(*); endclocking

  // Functional correctness
  ap_add: assert property ({cout, sum} == a + b + cin);

  // Basic coverage of carry behavior
  cp_cout0_cin0: cover property (cin == 1'b0 && cout == 1'b0);
  cp_cout1_cin0: cover property (cin == 1'b0 && cout == 1'b1);
  cp_cout0_cin1: cover property (cin == 1'b1 && cout == 1'b0);
  cp_cout1_cin1: cover property (cin == 1'b1 && cout == 1'b1);
endmodule

bind ripple_carry_adder ripple_carry_adder_sva rca_sva_bind (.*);

// -------------------------------------------
// detect_carry_adder SVA
// Note: p,g are 1-bit, while a,b are 2-bit. RTL assigns p=a&b and g=a|b,
// which truncates to bit[0]. We assert that exact implemented behavior.
// -------------------------------------------
module detect_carry_adder_sva (
  input logic [1:0] a,
  input logic [1:0] b,
  input logic       cin,
  input logic       p,
  input logic       g
);
  default clocking cb @(*); endclocking

  // Match RTL semantics (LSB truncation)
  ap_pg_match: assert property (
      p == (a & b)[0] && g == (a | b)[0]
  );

  // Logical implication on LSBs: (a&b) -> (a|b)
  ap_p_implies_g: assert property ( p |-> g );

  // Coverage of p/g space at LSB
  cp_p0g0: cover property (p == 1'b0 && g == 1'b0);
  cp_p0g1: cover property (p == 1'b0 && g == 1'b1);
  cp_p1g1: cover property (p == 1'b1 && g == 1'b1);
endmodule

bind detect_carry_adder detect_carry_adder_sva dca_sva_bind (.*);

// -------------------------------------------
// GDA_St_N8_M4_P2 SVA
// Binds internal signals to check add-chain, segment sums, detect-carry net relations.
// -------------------------------------------
module GDA_St_N8_M4_P2_sva (
  input  logic [7:0] in1,
  input  logic [7:0] in2,
  input  logic [7:0] res,

  // Internal nets we want to observe
  input  logic [1:0] temp1, temp2, temp3, temp4,
  input  logic       c2, c4, c6,
  input  logic       p0, p1, p2, p3, p4, p5,
  input  logic       g0, g1, g2, g3, g4, g5,
  input  logic       p1g0, p3g2, p5g4
);
  default clocking cb @(*); endclocking

  // Overall correctness: block implements in1+in2 (lower 8 bits)
  ap_overall_sum: assert property ( res == (in1 + in2) );

  // Segment sums and carries
  ap_seg0: assert property ( {c2, temp1} == ({1'b0, in1[1:0]} + {1'b0, in2[1:0]}) );
  ap_seg1: assert property ( {c4, temp2} == ({1'b0, in1[3:2]} + {1'b0, in2[3:2]} + c2) );
  ap_seg2: assert property ( {c6, temp3} == ({1'b0, in1[5:4]} + {1'b0, in2[5:4]} + c4) );
  ap_seg3: assert property ( temp4 == ({1'b0, in1[7:6]} + {1'b0, in2[7:6]} + c6)[1:0] );

  // res mapping to temps
  ap_res_map0: assert property ( res[1:0] == temp1 );
  ap_res_map1: assert property ( res[3:2] == temp2 );
  ap_res_map2: assert property ( res[5:4] == temp3 );
  ap_res_map3: assert property ( res[7:6] == temp4 );

  // Detect-carry module behavior (matches RTL truncation semantics)
  ap_dca0: assert property ( p0 == (in1[1:0] & in2[1:0])[0] && g0 == (in1[1:0] | in2[1:0])[0] );
  ap_dca1: assert property ( p1 == (in1[1:0] & in2[1:0])[0] && g1 == (in1[1:0] | in2[1:0])[0] );
  ap_dca2: assert property ( p2 == (in1[3:2] & in2[3:2])[0] && g2 == (in1[3:2] | in2[3:2])[0] );
  ap_dca3: assert property ( p3 == (in1[3:2] & in2[3:2])[0] && g3 == (in1[3:2] | in2[3:2])[0] );
  ap_dca4: assert property ( p4 == (in1[5:4] & in2[5:4])[0] && g4 == (in1[5:4] | in2[5:4])[0] );
  ap_dca5: assert property ( p5 == (in1[5:4] & in2[5:4])[0] && g5 == (in1[5:4] | in2[5:4])[0] );

  // Repeated detect instances with identical a/b must match (cin ignored by RTL)
  ap_eq10: assert property ( p1 == p0 && g1 == g0 );
  ap_eq32: assert property ( p3 == p2 && g3 == g2 );
  ap_eq54: assert property ( p5 == p4 && g5 == g4 );

  // Gating nets correctness
  ap_p1g0: assert property ( p1g0 == (p1 & g0) );
  ap_p3g2: assert property ( p3g2 == (p3 & g2) );
  ap_p5g4: assert property ( p5g4 == (p5 & g4) );

  // Coverage: exercise carry propagation and detect nets
  cp_c2:    cover property (c2);
  cp_c4:    cover property (c4);
  cp_c6:    cover property (c6);
  cp_pg10:  cover property (p1g0);
  cp_pg32:  cover property (p3g2);
  cp_pg54:  cover property (p5g4);
  // Overflow coverage (final 2-bit block carry-out)
  cp_top_overflow: cover property ( ({1'b0, in1[7:6]} + {1'b0, in2[7:6]} + c6) > 3 );
endmodule

bind GDA_St_N8_M4_P2 GDA_St_N8_M4_P2_sva gda_sva_bind (
  .in1(in1), .in2(in2), .res(res),
  .temp1(temp1), .temp2(temp2), .temp3(temp3), .temp4(temp4),
  .c2(c2), .c4(c4), .c6(c6),
  .p0(p0), .p1(p1), .p2(p2), .p3(p3), .p4(p4), .p5(p5),
  .g0(g0), .g1(g1), .g2(g2), .g3(g3), .g4(g4), .g5(g5),
  .p1g0(p1g0), .p3g2(p3g2), .p5g4(p5g4)
);