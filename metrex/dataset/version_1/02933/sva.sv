// SVA for connection_module
module connection_module_asserts (input logic a,b,c,select, w,x,y,z);

  // Functional mapping and mux behavior
  ap_map: assert property (@(a or b or c or select) ##0
     (w === a) && (z === c) &&
     ((select === 1'b0) |-> (x === b && y === c)) &&
     ((select === 1'b1) |-> (x === c && y === b)));

  // Consistency when b == c (independent of select)
  ap_b_eq_c: assert property (@(a or b or c or select) (b === c) |-> ##0 (x === b && y === b));

  // No-X when driving conditions are known
  ap_w_known:  assert property (@(a) !$isunknown(a) |-> ##0 (w === a));
  ap_z_known:  assert property (@(c) !$isunknown(c) |-> ##0 (z === c));
  ap_xy_known: assert property (@(a or b or c or select)
                                !$isunknown({b,c,select}) |-> ##0
                                ((select==1'b0) ? (x===b && y===c)
                                                : (x===c && y===b)));

  // If b != c and select known, x and y must differ
  ap_xy_diff: assert property (@(b or c or select)
                               (b !== c && !$isunknown(select)) |-> ##0 (x !== y));

  // Coverage
  cp_sel0:  cover property (@(a or b or c or select) (select==1'b0 && b!==c) ##0 (x===b && y===c));
  cp_sel1:  cover property (@(a or b or c or select) (select==1'b1 && b!==c) ##0 (x===c && y===b));
  cp_equal: cover property (@(a or b or c or select) (b===c) ##0 (x===y && x===b));
  cp_w_pass: cover property (@(a) $changed(a) ##0 (w===a));
  cp_z_pass: cover property (@(c) $changed(c) ##0 (z===c));
  cp_swap_on_sel_toggle: cover property (@(select)
                      !$isunknown({b,c}) && b!==c && $stable({b,c}) && $changed(select) ##0
                      ((select==0 && x===b && y===c) || (select==1 && x===c && y===b)));

endmodule

bind connection_module connection_module_asserts sva(.*);