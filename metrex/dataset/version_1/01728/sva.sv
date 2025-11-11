// SVA for sky130_fd_sc_ms__a22o
// Bind into the DUT to access internal sel
module sky130_fd_sc_ms__a22o_sva;

  // Power-good and known-control predicates
  wire rails_ok    = (VPWR === 1'b1) && (VGND === 1'b0);
  wire ctrls_known = rails_ok && !$isunknown({VPB,VNB,A1,A2});

  // Combinational equivalence and X-propagation checks
  always_comb begin
    if (rails_ok && !$isunknown({VPB,VNB})) begin
      assert (sel == (VPB & ~VNB))
        else $error("sel != VPB & ~VNB");
    end
    if (ctrls_known) begin
      assert (X == (sel ? A1 : A2))
        else $error("X != (sel ? A1 : A2)");
      assert (!$isunknown(X))
        else $error("X unknown while rails and controls are known");
    end
  end

  // Independence from unused inputs B1/B2
  property p_b1_indep;
    @(posedge B1 or negedge B1)
      rails_ok && $stable({A1,A2,VPB,VNB}) && !$isunknown({A1,A2,VPB,VNB})
      |-> $stable(X);
  endproperty
  assert property (p_b1_indep);

  property p_b2_indep;
    @(posedge B2 or negedge B2)
      rails_ok && $stable({A1,A2,VPB,VNB}) && !$isunknown({A1,A2,VPB,VNB})
      |-> $stable(X);
  endproperty
  assert property (p_b2_indep);

  // X changes only due to controlling inputs
  property p_x_change_cause;
    @(posedge X or negedge X)
      rails_ok |-> ($changed(A1) || $changed(A2) || $changed(VPB) || $changed(VNB));
  endproperty
  assert property (p_x_change_cause);

  // Functional consistency on controlling input changes (zero-delay)
  property p_func;
    @(posedge A1 or negedge A1 or
      posedge A2 or negedge A2 or
      posedge VPB or negedge VPB or
      posedge VNB or negedge VNB)
      ctrls_known |-> ##0 (X == (sel ? A1 : A2));
  endproperty
  assert property (p_func);

  // Coverage: both mux paths, propagation, and B1/B2 independence
  cover property (@(posedge VPB or negedge VNB) rails_ok && sel && !$isunknown(A1) && X==A1);
  cover property (@(negedge VPB or posedge VNB) rails_ok && !sel && !$isunknown(A2) && X==A2);
  cover property (@(posedge A1 or negedge A1) rails_ok && sel ##0 $changed(X));
  cover property (@(posedge A2 or negedge A2) rails_ok && !sel ##0 $changed(X));
  cover property (@(posedge B1 or negedge B1) rails_ok && $stable({A1,A2,VPB,VNB}) ##0 $stable(X));
  cover property (@(posedge B2 or negedge B2) rails_ok && $stable({A1,A2,VPB,VNB}) ##0 $stable(X));

endmodule

bind sky130_fd_sc_ms__a22o sky130_fd_sc_ms__a22o_sva a22o_sva();