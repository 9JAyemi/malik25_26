// SVA for oh_reg1 — concise, high-quality checks and coverage
module oh_reg1_sva #(parameter int DW=1)
(
  input logic               nreset,
  input logic               clk,
  input logic               en,
  input logic [DW-1:0]      in,
  input logic [DW-1:0]      out
);

  // Basic sanity
  initial assert (DW > 0) else $fatal(1, "DW must be > 0");

  // Default clocking
  default clocking cb @(posedge clk); endclocking

  // Reset behavior: output forced to 0 whenever reset is low and on first clk after assert
  assert property (@(posedge clk) !nreset |-> out == '0);
  assert property (@(posedge clk) $fell(nreset) |=> out == '0);

  // No X/Z when active; no X/Z written
  assert property (disable iff (!nreset) !$isunknown(out));
  assert property (disable iff (!nreset) en |-> !$isunknown(in));

  // Write semantics: capture in on en; hold otherwise
  assert property (disable iff (!nreset) en  |=> out === $past(in));
  assert property (disable iff (!nreset) !en |=> out === $past(out));

  // Back-to-back writes behave consistently
  assert property (disable iff (!nreset) en ##1 en |=> out === $past(in));

  // Coverage
  cover  property (@(posedge clk) !nreset ##1 nreset); // reset pulse observed
  cover  property (disable iff (!nreset)
                   en && (in !== $past(out)) ##1 (out === $past(in))); // a write that changes out
  cover  property (disable iff (!nreset)
                   !en ##1 (out === $past(out)) && (in !== $past(in))); // hold while in toggles
  cover  property (disable iff (!nreset)
                   en ##1 (out === $past(in)) ##1 en ##1 (out === $past(in))); // back-to-back writes

endmodule

// Bind into DUT
bind oh_reg1 oh_reg1_sva #(.DW(DW)) oh_reg1_sva_b (.nreset(nreset), .clk(clk), .en(en), .in(in), .out(out));