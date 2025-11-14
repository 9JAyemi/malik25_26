// SVA for sky130_fd_sc_lp__a22o_m / _1 (as implemented: X = (A1&A2) & (B1&B2))

// I/O-level functional and power checks
module sky130_fd_sc_lp__a22o_io_sva (
  input logic A1, A2, B1, B2,
  input logic VPWR, VGND, VPB, VNB,
  input logic X
);
  wire pgood = (VPWR===1'b1) && (VGND===1'b0);

  // Body-bias pins tied correctly to rails
  assert property (@(VPWR or VPB) VPB === VPWR);
  assert property (@(VGND or VNB) VNB === VGND);

  // Functional equivalence when inputs are known
  assert property (@(A1 or A2 or B1 or B2 or X or VPWR or VGND)
                   disable iff (!pgood)
                   (!$isunknown({A1,A2,B1,B2})) |-> (X == ((A1 & A2) & (B1 & B2))));

  // Dominating zero: any 0 input forces X=0
  assert property (@(A1 or A2 or B1 or B2 or X or VPWR or VGND)
                   disable iff (!pgood)
                   ((A1==1'b0) || (A2==1'b0) || (B1==1'b0) || (B2==1'b0)) |-> (X==1'b0));

  // If X is 1, all inputs must be 1
  assert property (@(A1 or A2 or B1 or B2 or X or VPWR or VGND)
                   disable iff (!pgood)
                   (X==1'b1) |-> (A1 && A2 && B1 && B2));

  // Output must be known when inputs are known
  assert property (@(A1 or A2 or B1 or B2 or X or VPWR or VGND)
                   disable iff (!pgood)
                   (!$isunknown({A1,A2,B1,B2})) |-> !$isunknown(X));

  // Coverage: key truth-table regions under good power
  cover property (@(A1 or A2 or B1 or B2)
                  pgood && (A1 && A2 && B1 && B2) && (X==1));
  cover property (@(A1 or A2 or B1 or B2)
                  pgood && (A1 && A2) && !(B1 && B2) && (X==0));
  cover property (@(A1 or A2 or B1 or B2)
                  pgood && !(A1 && A2) && (B1 && B2) && (X==0));
  cover property (@(A1 or A2 or B1 or B2)
                  pgood && !(A1 && A2) && !(B1 && B2) && (X==0));
endmodule

// Structural checks for the _1 implementation internals
module sky130_fd_sc_lp__a22o_struct_sva;
  wire pgood = (VPWR===1'b1) && (VGND===1'b0);

  // Check each primitive’s function when its inputs are known
  assert property (@(A1 or A2 or an_a1)
                   disable iff (!pgood)
                   (!$isunknown({A1,A2})) |-> (an_a1 === ~(A1 & A2)));
  assert property (@(B1 or B2 or an_b1)
                   disable iff (!pgood)
                   (!$isunknown({B1,B2})) |-> (an_b1 === ~(B1 & B2)));
  assert property (@(an_a1 or an_b1 or s_ann12)
                   disable iff (!pgood)
                   (!$isunknown({an_a1,an_b1})) |-> (s_ann12 === (an_a1 | an_b1)));
  assert property (@(s_ann12 or X)
                   disable iff (!pgood)
                   (!$isunknown(s_ann12)) |-> (X === ~s_ann12));
endmodule

// Bind assertions to DUTs
bind sky130_fd_sc_lp__a22o_m  sky130_fd_sc_lp__a22o_io_sva     a22o_m_io_sva (.*);
bind sky130_fd_sc_lp__a22o_1  sky130_fd_sc_lp__a22o_io_sva     a22o_1_io_sva (.*);
bind sky130_fd_sc_lp__a22o_1  sky130_fd_sc_lp__a22o_struct_sva a22o_1_struct_sva ();