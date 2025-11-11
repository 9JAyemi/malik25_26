// SVA for glitch_filter
// Focused, bind-ready, with key checks and compact coverage.

module glitch_filter_sva #(parameter int p=5, q=2)
(
  input logic clk,
  input logic in,
  input logic out,
  input logic [p-1:0] delay_line
);

  // Parameter legality (static)
  initial begin
    assert(p >= 2) else $error("glitch_filter: p must be >= 2");
    assert(q >= 1) else $error("glitch_filter: q must be >= 1");
    assert(p >= q+1) else $error("glitch_filter: p must be >= q+1");
  end

  // Past-valid helper
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Delay-line shifting correctness
  property shift_correct;
    past_valid |-> delay_line == { $past(delay_line[p-2:0]), $past(in) };
  endproperty
  assert property (shift_correct);

  // No update when in == tap(p-1)
  property hold_when_equal;
    past_valid && $past(in) == $past(delay_line[p-1])
      |=> out == $past(out);
  endproperty
  assert property (hold_when_equal);

  // Normal update (no glitch): in != tap(p-1) and in != tap(p-q-1) -> out = tap(p-1)
  property update_normal;
    past_valid
    && $past(in) != $past(delay_line[p-1])
    && $past(in) != $past(delay_line[p-q-1])
      |=> out == $past(delay_line[p-1]);
  endproperty
  assert property (update_normal);

  // Glitch-removal update: in != tap(p-1) and in == tap(p-q-1) -> out = tap(p-2)
  property update_glitch;
    past_valid
    && $past(in) != $past(delay_line[p-1])
    && $past(in) == $past(delay_line[p-q-1])
      |=> out == $past(delay_line[p-2]);
  endproperty
  assert property (update_glitch);

  // Out only changes when in != tap(p-1)
  property out_changes_only_when_needed;
    past_valid && (out != $past(out)) |-> $past(in) != $past(delay_line[p-1]);
  endproperty
  assert property (out_changes_only_when_needed);

  // Compact functional coverage of all paths
  cover property (past_valid && $past(in) == $past(delay_line[p-1]) |=> out == $past(out));               // hold path
  cover property (past_valid && $past(in) != $past(delay_line[p-1]) && $past(in) != $past(delay_line[p-q-1]) |=> out == $past(delay_line[p-1])); // normal
  cover property (past_valid && $past(in) != $past(delay_line[p-1]) && $past(in) == $past(delay_line[p-q-1]) |=> out == $past(delay_line[p-2])); // glitch
  cover property (past_valid |=> delay_line == { $past(delay_line[p-2:0]), $past(in) });                   // shift seen

endmodule

// Bind to DUT (accesses internal delay_line)
bind glitch_filter glitch_filter_sva #(.p(p), .q(q)) gf_sva (
  .clk(clk),
  .in(in),
  .out(out),
  .delay_line(delay_line)
);