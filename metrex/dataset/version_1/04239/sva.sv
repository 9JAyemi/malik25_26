// SVA for sky130_fd_sc_hd__a32o
module sky130_fd_sc_hd__a32o_sva (sky130_fd_sc_hd__a32o m);

  default clocking cb @(
      posedge m.A1 or negedge m.A1 or
      posedge m.A2 or negedge m.A2 or
      posedge m.A3 or negedge m.A3 or
      posedge m.B1 or negedge m.B1 or
      posedge m.B2 or negedge m.B2
  ); endclocking

  // Shorthand terms
  let tA = (m.A1 & m.A2 & m.A3);
  let tB = (m.B1 & m.B2);
  let tY = (tA | tB);

  // Functional equivalence
  assert property (m.X === tY);

  // Internal net correctness
  assert property (m.and0_out  === tA);
  assert property (m.and1_out  === tB);
  assert property (m.or0_out_X === (m.and1_out | m.and0_out));
  assert property (m.X         === m.or0_out_X);

  // No spurious toggles; edges align with function
  assert property ($stable(tY) |-> $stable(m.X));
  assert property ($rose(tY)   |-> $rose(m.X));
  assert property ($fell(tY)   |-> $fell(m.X));

  // Known-ness when inputs are known
  assert property ((!$isunknown({m.A1,m.A2,m.A3,m.B1,m.B2}))
                   |-> (!$isunknown(m.and0_out) &&
                        !$isunknown(m.and1_out) &&
                        !$isunknown(m.or0_out_X) &&
                        !$isunknown(m.X)));

  // Coverage: exercise each term, both terms, and X edges
  cover property ( tA && !tB );
  cover property (!tA &&  tB );
  cover property ( tA &&  tB );
  cover property ($rose(m.X));
  cover property ($fell(m.X));

endmodule

bind sky130_fd_sc_hd__a32o sky130_fd_sc_hd__a32o_sva a32o_sva();