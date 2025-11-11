// SVA for mux4to1. Bind this to the DUT.
// Focuses on functional equivalence, data isolation, and path-follow behavior,
// with concise full coverage.

module mux4to1_sva (
  input logic       q,
  input logic       i0,
  input logic       i1,
  input logic       i2,
  input logic       i3,
  input logic [1:0] sel
);

  function automatic logic sel_data(input logic i0,i1,i2,i3, input logic [1:0] sel);
    case (sel)
      2'b00: sel_data = i0;
      2'b01: sel_data = i1;
      2'b10: sel_data = i2;
      default: sel_data = i3;
    endcase
  endfunction

  // Functional correctness: q must equal the 4:1 mux truth-table when all known.
  property p_functional;
    @(i0 or i1 or i2 or i3 or sel[0] or sel[1])
      !$isunknown({sel,i0,i1,i2,i3}) |-> ##0 (q === sel_data(i0,i1,i2,i3,sel));
  endproperty
  assert property (p_functional)
    else $error("mux4to1 mismatch: sel=%b exp=%0b q=%0b", sel, sel_data(i0,i1,i2,i3,sel), q);

  // Isolation: unselected input changes must not affect q (with sel and selected input stable).
  property p_no_impact_unselected;
    @(i0 or i1 or i2 or i3)
      !$isunknown({sel,i0,i1,i2,i3}) && $stable(sel) && $stable(sel_data(i0,i1,i2,i3,sel))
      |-> ##0 $stable(q);
  endproperty
  assert property (p_no_impact_unselected);

  // Follow: when only the selected input changes (sel stable), q must immediately follow it.
  property p_follows_selected;
    @(i0 or i1 or i2 or i3)
      !$isunknown({sel,i0,i1,i2,i3}) && $stable(sel) && $changed(sel_data(i0,i1,i2,i3,sel))
      |-> ##0 (q === sel_data(i0,i1,i2,i3,sel));
  endproperty
  assert property (p_follows_selected);

  // On sel change with data stable, q must immediately reflect the new selection.
  property p_on_sel_change;
    @(sel[0] or sel[1])
      !$isunknown({sel,i0,i1,i2,i3}) && $changed(sel) && $stable({i0,i1,i2,i3})
      |-> ##0 (q === sel_data(i0,i1,i2,i3,sel));
  endproperty
  assert property (p_on_sel_change);

  // Coverage: exercise all sel values.
  cover property (@(sel[0] or sel[1]) sel == 2'b00);
  cover property (@(sel[0] or sel[1]) sel == 2'b01);
  cover property (@(sel[0] or sel[1]) sel == 2'b10);
  cover property (@(sel[0] or sel[1]) sel == 2'b11);

  // Coverage: observe selected-path effect for each leg.
  cover property (@(i0) sel==2'b00 && !$isunknown({sel,i0}) ##0 q===i0);
  cover property (@(i1) sel==2'b01 && !$isunknown({sel,i1}) ##0 q===i1);
  cover property (@(i2) sel==2'b10 && !$isunknown({sel,i2}) ##0 q===i2);
  cover property (@(i3) sel==2'b11 && !$isunknown({sel,i3}) ##0 q===i3);

endmodule

bind mux4to1 mux4to1_sva u_mux4to1_sva(.q(q), .i0(i0), .i1(i1), .i2(i2), .i3(i3), .sel(sel));