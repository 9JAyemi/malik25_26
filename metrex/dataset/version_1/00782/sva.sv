// SVA for two_to_one_mux
// Focus: correctness for known select, X-prop behavior for unknown select, and concise coverage.

`default_nettype none

module two_to_one_mux_sva (
  input logic A,
  input logic B,
  input logic S,
  input logic Y
);

  // Functional correctness when select is known
  property p_sel0;  @(A or B or S) (S === 1'b0) |-> ##0 (Y === A); endproperty
  property p_sel1;  @(A or B or S) (S === 1'b1) |-> ##0 (Y === B); endproperty
  a_sel0: assert property(p_sel0);
  a_sel1: assert property(p_sel1);

  // X-propagation semantics when select is unknown
  property p_unknownS_same; @(A or B or S) $isunknown(S) && (A === B) |-> ##0 (Y === A); endproperty
  property p_unknownS_diff; @(A or B or S) $isunknown(S) && (A !== B) |-> ##0 $isunknown(Y); endproperty
  a_unknownS_same: assert property(p_unknownS_same);
  a_unknownS_diff: assert property(p_unknownS_diff);

  // Output changes are explained only by selected input or select
  property p_change_sel0; @(A or B or S or Y) (S === 1'b0 && $changed(Y)) |-> ($changed(A) || $changed(S)); endproperty
  property p_change_sel1; @(A or B or S or Y) (S === 1'b1 && $changed(Y)) |-> ($changed(B) || $changed(S)); endproperty
  a_change_sel0: assert property(p_change_sel0);
  a_change_sel1: assert property(p_change_sel1);

  // Coverage: both select values, unknown select cases, and data-follow behavior
  c_sel0:          cover property(@(A or B or S) (S === 1'b0) ##0 (Y === A));
  c_sel1:          cover property(@(A or B or S) (S === 1'b1) ##0 (Y === B));
  c_unknown_same:  cover property(@(A or B or S) $isunknown(S) && (A === B) ##0 (Y === A));
  c_unknown_diff:  cover property(@(A or B or S) $isunknown(S) && (A !== B) ##0 $isunknown(Y));
  c_follow_A:      cover property(@(posedge A or negedge A) (S === 1'b0) ##0 $changed(Y));
  c_follow_B:      cover property(@(posedge B or negedge B) (S === 1'b1) ##0 $changed(Y));
  c_switch_sel:    cover property(@(posedge S or negedge S) 1'b1 ##0 (Y === (S ? B : A)));

endmodule

// Bind the SVA module to the DUT
bind two_to_one_mux two_to_one_mux_sva sva_i (.*);

`default_nettype wire