// SVA for mux_buffer: concise, high-quality checks and coverage
// Bind this checker to the DUT.

module mux_buffer_sva(input logic I0, I1, S, O);

  // Continuous functional equivalence (matches 4-state Verilog ?: semantics)
  always_comb
    assert #0 (O === (S ? I0 : I1))
      else $error("mux_buffer: O != (S ? I0 : I1)");

  // When selected, output must track the selected input edges (with ##0 to avoid races)
  property p_track_i0;
    @(posedge I0 or negedge I0) S |-> ##0 (O == I0);
  endproperty
  a_track_i0: assert property (p_track_i0);

  property p_track_i1;
    @(posedge I1 or negedge I1) !S |-> ##0 (O == I1);
  endproperty
  a_track_i1: assert property (p_track_i1);

  // Known selected input implies known output
  property p_known_when_selected;
    @(posedge S or negedge S or posedge I0 or negedge I0 or posedge I1 or negedge I1)
      (((S && !$isunknown(I0)) || (!S && !$isunknown(I1)))) |-> ##0 !$isunknown(O);
  endproperty
  a_known_when_selected: assert property (p_known_when_selected);

  // Coverage: exercise both selections and data-path tracking/toggling
  c_sel1:      cover property (@(posedge S) ##0 (O == I0));
  c_sel0:      cover property (@(negedge S) ##0 (O == I1));
  c_track_i0:  cover property (@(posedge I0 or negedge I0) (S && ##0 (O == I0)));
  c_track_i1:  cover property (@(posedge I1 or negedge I1) (!S && ##0 (O == I1)));
  c_tog_sel_up:   cover property (@(posedge S) (!$isunknown({I0,I1}) && (I0 != I1)) ##0 $changed(O));
  c_tog_sel_down: cover property (@(negedge S) (!$isunknown({I0,I1}) && (I0 != I1)) ##0 $changed(O));

endmodule

bind mux_buffer mux_buffer_sva sva(.I0(I0), .I1(I1), .S(S), .O(O));