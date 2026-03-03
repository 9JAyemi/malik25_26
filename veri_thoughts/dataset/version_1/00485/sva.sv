// SVA for mux4to1
// Concise, high-quality checks + coverage. Bind into DUT.

module mux4to1_sva (
  input logic a,
  input logic b,
  input logic c,
  input logic d,
  input logic [1:0] sel,
  input logic y
);

  // Control must be known (no X/Z on select)
  ap_sel_known: assert property (@(sel) !$isunknown(sel));

  // Functional correctness (combinational; sample after ##0 to avoid delta races)
  ap_func: assert property (@(a or b or c or d or sel)
                            ##0 ( y === (sel==2'b00 ? a
                                         : sel==2'b01 ? b
                                         : sel==2'b10 ? c
                                         : d)));

  // Output must not change due to unselected input toggles (with sel and selected input stable)
  ap_ng00: assert property (@(a or b or c or d or sel)
                            (sel==2'b00 && !$changed({a,sel}) && ($changed(b) || $changed(c) || $changed(d)))
                            |-> ##0 $stable(y));
  ap_ng01: assert property (@(a or b or c or d or sel)
                            (sel==2'b01 && !$changed({b,sel}) && ($changed(a) || $changed(c) || $changed(d)))
                            |-> ##0 $stable(y));
  ap_ng10: assert property (@(a or b or c or d or sel)
                            (sel==2'b10 && !$changed({c,sel}) && ($changed(a) || $changed(b) || $changed(d)))
                            |-> ##0 $stable(y));
  ap_ng11: assert property (@(a or b or c or d or sel)
                            (sel==2'b11 && !$changed({d,sel}) && ($changed(a) || $changed(b) || $changed(c)))
                            |-> ##0 $stable(y));

  // Any y change must have a cause (sel change or selected input change)
  ap_y_change_has_cause: assert property (@(a or b or c or d or sel or y)
                        $changed(y) |-> ##0 ( $changed(sel)
                                           || (sel==2'b00 && $changed(a))
                                           || (sel==2'b01 && $changed(b))
                                           || (sel==2'b10 && $changed(c))
                                           || (sel==2'b11 && $changed(d)) ));

  // Coverage: each select value observed
  cp_sel00: cover property (@(sel) sel==2'b00);
  cp_sel01: cover property (@(sel) sel==2'b01);
  cp_sel10: cover property (@(sel) sel==2'b10);
  cp_sel11: cover property (@(sel) sel==2'b11);

  // Coverage: each mapping exercised
  cp_y_eq_a: cover property (@(a or sel) (sel==2'b00) && ##0 (y === a));
  cp_y_eq_b: cover property (@(b or sel) (sel==2'b01) && ##0 (y === b));
  cp_y_eq_c: cover property (@(c or sel) (sel==2'b10) && ##0 (y === c));
  cp_y_eq_d: cover property (@(d or sel) (sel==2'b11) && ##0 (y === d));

endmodule

bind mux4to1 mux4to1_sva sva_mux4to1 (.*);