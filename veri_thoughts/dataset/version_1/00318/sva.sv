Below is a concise SVA bind module that thoroughly checks function, X-propagation, and provides useful coverage. It uses @(*) sampling with ##0 to evaluate post-combinational updates.

`ifndef SYNTHESIS
module mux_4to1_case_sva (
  input logic a, b, c, d,
  input logic sel0, sel1,
  input logic out
);

  // 1) Functional correctness when all relevant inputs are known
  assert property (@(*)
    !$isunknown({sel1,sel0,a,b,c,d}) |-> ##0
      (out == (sel1 ? (sel0 ? d : c) : (sel0 ? b : a)))
  ) else $error("MUX functional mismatch");

  // 2) Selector must be known (avoid latchy/incomplete case on X/Z selects)
  assert property (@(*)
    !$isunknown({sel1,sel0})
  ) else $error("Selector contains X/Z (incomplete case coverage)");

  // 3) X-propagation from selected data input when selector is known
  assert property (@(*)
    ({sel1,sel0}==2'b00 && !$isunknown({sel1,sel0}) && $isunknown(a)) |-> ##0 $isunknown(out)
  );
  assert property (@(*)
    ({sel1,sel0}==2'b01 && !$isunknown({sel1,sel0}) && $isunknown(b)) |-> ##0 $isunknown(out)
  );
  assert property (@(*)
    ({sel1,sel0}==2'b10 && !$isunknown({sel1,sel0}) && $isunknown(c)) |-> ##0 $isunknown(out)
  );
  assert property (@(*)
    ({sel1,sel0}==2'b11 && !$isunknown({sel1,sel0}) && $isunknown(d)) |-> ##0 $isunknown(out)
  );

  // 4) Coverage: exercise each select value
  cover property (@(*) {sel1,sel0}==2'b00);
  cover property (@(*) {sel1,sel0}==2'b01);
  cover property (@(*) {sel1,sel0}==2'b10);
  cover property (@(*) {sel1,sel0}==2'b11);

  // 5) Coverage: when select is stable, out follows the selected input toggle
  cover property (@(*)
    $stable({sel1,sel0}) && {sel1,sel0}==2'b00 && $changed(a) ##0 $changed(out)
  );
  cover property (@(*)
    $stable({sel1,sel0}) && {sel1,sel0}==2'b01 && $changed(b) ##0 $changed(out)
  );
  cover property (@(*)
    $stable({sel1,sel0}) && {sel1,sel0}==2'b10 && $changed(c) ##0 $changed(out)
  );
  cover property (@(*)
    $stable({sel1,sel0}) && {sel1,sel0}==2'b11 && $changed(d) ##0 $changed(out)
  );

endmodule

// Bind into the DUT
bind mux_4to1_case mux_4to1_case_sva u_mux_4to1_case_sva (
  .a(a), .b(b), .c(c), .d(d),
  .sel0(sel0), .sel1(sel1),
  .out(out)
);
`endif