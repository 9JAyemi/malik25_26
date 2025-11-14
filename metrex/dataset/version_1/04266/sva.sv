module mux_2to1_sva (
  input logic A,
  input logic B,
  input logic sel,
  input logic out
);

  // Sample on any relevant edge (including out to catch spurious changes)
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge sel or negedge sel or
    posedge out or negedge out
  ); endclocking

  // Functional correctness (4-state semantics, match RTL)
  assert property (1 |-> ##0 (out === ((sel == 1'b0) ? A : B)));

  // Out only changes when selected input or select changes
  assert property (
    $changed(out) |-> (
      $changed(sel) ||
      (($past(sel)===1'b0) && $changed(A)) ||
      (($past(sel)===1'b1) && $changed(B))
    )
  );

  // X/Z on sel: merge semantics
  assert property (
    (sel !== 1'b0 && sel !== 1'b1 && !$isunknown(A) && !$isunknown(B) && (A !== B))
    |-> ##0 $isunknown(out)
  );
  assert property (
    (sel !== 1'b0 && sel !== 1'b1 && !$isunknown(A) && (A === B))
    |-> ##0 (out === A)
  );

  // Coverage
  cover property (sel===1'b0 ##0 $changed(A) ##0 (out===A));
  cover property (sel===1'b1 ##0 $changed(B) ##0 (out===B));
  cover property ((sel !== 1'b0 && sel !== 1'b1 && !$isunknown(A) && !$isunknown(B) && (A !== B)) ##0 $isunknown(out));
  cover property ((sel !== 1'b0 && sel !== 1'b1 && !$isunknown(A) && (A === B)) ##0 (out===A));

endmodule

bind mux_2to1 mux_2to1_sva mux_2to1_sva_i (.*);