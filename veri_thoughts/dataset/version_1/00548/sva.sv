// SVA for output_select. Bind this module to the DUT.
module output_select_sva(
  input sel,
  input [7:0] out1,
  input [7:0] out2,
  input [7:0] out
);
  // Sample on any relevant change (combinational)
  default clocking cb @(sel or out1 or out2 or out); endclocking

  // Functional correctness (matches procedural semantics)
  a_sel0:      assert property (sel === 1'b0 |-> out === out1);
  a_sel1:      assert property (sel === 1'b1 |-> out === out2);
  // With sel X/Z, (sel==0) is X -> else branch taken
  a_selx_else: assert property ((sel !== 1'b0 && sel !== 1'b1) |-> out === out2);

  // No unexpected X on out when selected input and sel are known
  a_no_x0: assert property (sel===1'b0 && !$isunknown(out1) |-> !$isunknown(out));
  a_no_x1: assert property (sel===1'b1 && !$isunknown(out2) |-> !$isunknown(out));

  // Out changes only when select or selected input changes
  a_out_cause: assert property (
    $changed(out) |-> $changed(sel) ||
                   (sel===1'b0 && $changed(out1)) ||
                   (sel===1'b1 && $changed(out2)) ||
                   ((sel!==1'b0 && sel!==1'b1) && $changed(out2))
  );

  // Stability when selected source and sel are stable
  a_stable0: assert property (sel===1'b0 && $stable(out1) && $stable(sel) |-> $stable(out));
  a_stable1: assert property (sel===1'b1 && $stable(out2) && $stable(sel) |-> $stable(out));

  // Coverage
  c_path0:       cover property (sel===1'b0 && out===out1);
  c_path1:       cover property (sel===1'b1 && out===out2);
  c_sel_pos:     cover property (@(posedge sel) out===out2);
  c_sel_neg:     cover property (@(negedge sel) out===out1);
  c_data_path0:  cover property (@(out1) sel===1'b0 && $changed(out));
  c_data_path1:  cover property (@(out2) sel===1'b1 && $changed(out));
endmodule

// Example bind
bind output_select output_select_sva output_select_sva_i(.sel(sel), .out1(out1), .out2(out2), .out(out));