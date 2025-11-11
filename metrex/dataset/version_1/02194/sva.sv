// SVA checker for top_module
module top_module_sva (
    input  logic clk,
    input  logic a,
    input  logic b,
    input  logic sel_b1,
    input  logic sel_b2,
    input  logic q,
    input  logic mux_out
);
  default clocking cb @(posedge clk); endclocking

  // guard for $past
  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Combinational mux correctness
  assert property (mux_out == (sel_b1 ? b : a))
    else $error("MUX mismatch: mux_out != sel?b:a");

  // DFF captures previous mux_out
  assert property (q == $past(mux_out))
    else $error("DFF mismatch: q != $past(mux_out)");

  // End-to-end behavior (sel_b2 has no functional effect)
  assert property (q == $past(sel_b1 ? b : a))
    else $error("End-to-end mismatch: q != $past(sel?b:a)");

  // q only changes on clk rising edge
  assert property (disable iff (!past_valid) @(posedge q) $rose(clk))
    else $error("q rose without clk rising edge");
  assert property (disable iff (!past_valid) @(negedge q) $rose(clk))
    else $error("q fell without clk rising edge");

  // X-propagation sanity
  assert property (!$isunknown({a,b,sel_b1}) |-> !$isunknown(mux_out))
    else $error("MUX produced X from known inputs");
  assert property (!$isunknown($past(mux_out)) |-> !$isunknown(q))
    else $error("DFF produced X from known input");

  // sel_b2 is unused: if only sel_b2 changes, outputs remain stable
  assert property (($changed(sel_b2) && $stable(a) && $stable(b) && $stable(sel_b1))
                   |-> ($stable(mux_out) && $stable(q)))
    else $error("sel_b2 affected outputs (should be unused)");

  // Coverage
  cover property (!sel_b1 ##1 q == $past(a));
  cover property ( sel_b1 ##1 q == $past(b));
  cover property ($rose(sel_b1));
  cover property ($fell(sel_b1));
  cover property ($rose(sel_b2));
  cover property ($fell(sel_b2));
  cover property (q != $past(q)); // q toggles
endmodule

// Bind into DUT; tap internal mux output
bind top_module top_module_sva i_top_module_sva (
  .clk(clk),
  .a(a),
  .b(b),
  .sel_b1(sel_b1),
  .sel_b2(sel_b2),
  .q(q),
  .mux_out(mux_inst.out)
);