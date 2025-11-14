// SVA checker for mux_2to1
module mux_2to1_sva(input logic A, B, S, Y);

  // Functional check with X-aware ternary; evaluated after delta
  always @* begin
    assert #0 (Y === (S ? A : B))
      else $error("mux_2to1 func mismatch: S=%b A=%b B=%b Y=%b", S,A,B,Y);
  end

  // Output changes only when some input changes
  property p_y_changes_only_on_input;
    @(A or B or S or Y) $changed(Y) |-> $changed({A,B,S});
  endproperty
  assert property(p_y_changes_only_on_input);

  // If inputs are known, output must be known
  property p_known_out_when_known_in;
    @(A or B or S or Y) !$isunknown({A,B,S}) |-> !$isunknown(Y);
  endproperty
  assert property(p_known_out_when_known_in);

  // Selected input must affect Y (no delay), unselected must not (when S stable)
  property p_sel_A_propagates;   @(A or B or S or Y)
    (S==1 && !$changed(S) && $changed(A)) |-> ##0 $changed(Y);
  endproperty
  assert property(p_sel_A_propagates);

  property p_unsel_B_no_effect;  @(A or B or S or Y)
    (S==1 && !$changed(S) && $changed(B)) |-> ##0 !$changed(Y);
  endproperty
  assert property(p_unsel_B_no_effect);

  property p_sel_B_propagates;   @(A or B or S or Y)
    (S==0 && !$changed(S) && $changed(B)) |-> ##0 $changed(Y);
  endproperty
  assert property(p_sel_B_propagates);

  property p_unsel_A_no_effect;  @(A or B or S or Y)
    (S==0 && !$changed(S) && $changed(A)) |-> ##0 !$changed(Y);
  endproperty
  assert property(p_unsel_A_no_effect);

  // Coverage: both data paths, select values, and select toggles
  cover property (@(A or B or S or Y) (S==0) ##0 (Y==B));
  cover property (@(A or B or S or Y) (S==1) ##0 (Y==A));
  cover property (@(A or B or S or Y) (S==1 && $changed(A)) ##0 $changed(Y));
  cover property (@(A or B or S or Y) (S==0 && $changed(B)) ##0 $changed(Y));
  cover property (@(A or B or S or Y) (A!=B) and $rose(S) ##0 $changed(Y));
  cover property (@(A or B or S or Y) (A!=B) and $fell(S) ##0 $changed(Y));

endmodule

bind mux_2to1 mux_2to1_sva mux_2to1_sva_i (.*);