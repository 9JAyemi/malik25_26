// SVA for sky130_fd_sc_ls__o22a: X = (A1 | A2) & (B1 | B2)
module sky130_fd_sc_ls__o22a_sva;

  // Power pins must be at legal constants
  assert property (VPWR === 1'b1 && VPB === 1'b1 && VGND === 1'b0 && VNB === 1'b0);

  // Functional equivalence when inputs are known (allow 0-time settle)
  always @* begin
    logic exp = (A1 | A2) & (B1 | B2);
    if (!$isunknown({A1,A2,B1,B2})) assert #0 (X === exp);
  end

  // Internal decomposition checks (when drivers known)
  always @* begin
    if (!$isunknown({A1,A2}))            assert #0 (or0_out     === (A1 | A2));
    if (!$isunknown({B1,B2}))            assert #0 (or1_out     === (B1 | B2));
    if (!$isunknown({or0_out,or1_out}))  assert #0 (and0_out_X  === (or0_out & or1_out));
                                          assert #0 (X          === and0_out_X);
  end

  // Safety: X high implies both OR groups high (when all known)
  property p_x_high_cond;
    !$isunknown({A1,A2,B1,B2,X}) && (X == 1) |-> ((A1 | A2) && (B1 | B2));
  endproperty
  assert property (p_x_high_cond);

  // Safety: if either group is 0, X must be 0 (when inputs known)
  property p_x_low_cond;
    !$isunknown({A1,A2,B1,B2}) && ((~(A1|A2)) || (~(B1|B2))) |-> (X == 0);
  endproperty
  assert property (p_x_low_cond);

  // Coverage: four minimal 1-cases
  cover property (!$isunknown({A1,A2,B1,B2}) &&  A1 &&  B1 && !A2 && !B2 &&  X);
  cover property (!$isunknown({A1,A2,B1,B2}) &&  A1 &&  B2 && !A2 && !B1 &&  X);
  cover property (!$isunknown({A1,A2,B1,B2}) &&  A2 &&  B1 && !A1 && !B2 &&  X);
  cover property (!$isunknown({A1,A2,B1,B2}) &&  A2 &&  B2 && !A1 && !B1 &&  X);

  // Coverage: corner 0/1 cases and X edges
  cover property (!$isunknown({A1,A2,B1,B2}) && !A1 && !A2 && !B1 && !B2 && !X);
  cover property (!$isunknown({A1,A2,B1,B2}) &&  A1 &&  A2 &&  B1 &&  B2 &&  X);
  cover property (!$isunknown({A1,A2,B1,B2,X}) && $rose(X));
  cover property (!$isunknown({A1,A2,B1,B2,X}) && $fell(X));

endmodule

bind sky130_fd_sc_ls__o22a sky130_fd_sc_ls__o22a_sva sva_o22a();