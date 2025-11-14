// SVA for edge_detector, mux, and top_module.
// Concise, high-signal-coverage, bind-ready.

module edge_detector_sva (edge_detector d);
  default clocking cb @(posedge d.clk); endclocking
  bit past_valid;
  initial past_valid = 0;
  always @(posedge d.clk) past_valid <= 1;

  // On any input change, out updates (1-cycle observable due to NBA)
  assert property (past_valid && (d.in !== $past(d.in)) |-> ##1 d.out == $past(d.in))
    else $error("edge_detector: out did not capture current in after change");

  // When input is stable, out holds its value
  assert property (past_valid && (d.in === $past(d.in)) |-> d.out == $past(d.out))
    else $error("edge_detector: out changed without input change");

  // prev_in must always track prior in
  assert property (past_valid |-> d.prev_in == $past(d.in))
    else $error("edge_detector: prev_in != $past(in)");

  // Knownness after a change
  assert property (past_valid && (d.in !== $past(d.in)) |-> ##1 !$isunknown(d.out))
    else $error("edge_detector: out unknown after change");

  // Coverage: up/down changes and holds
  cover property (past_valid && ($past(d.in) < d.in));
  cover property (past_valid && ($past(d.in) > d.in));
  cover property (past_valid && (d.in === $past(d.in)));
endmodule


module mux_sva (mux m);
  // Disallow X/Z on selects (prevents latch-like behavior)
  always @* assert (!$isunknown({m.sel_b1, m.sel_b2}))
    else $error("mux: select has X/Z");

  // Functional mapping for valid selects
  always @* if (!$isunknown({m.sel_b1, m.sel_b2})) begin
    assert (m.out == (m.sel_b1 ? (m.sel_b2 ? m.in4 : m.in3)
                               : (m.sel_b2 ? m.in2 : m.in1)))
      else $error("mux: out != selected input");
  end

  // Coverage: hit all 4 select combinations
  cover property (@(m.sel_b1 or m.sel_b2) {!$isunknown({m.sel_b1,m.sel_b2}) && {m.sel_b1,m.sel_b2}==2'b00});
  cover property (@(m.sel_b1 or m.sel_b2) {!$isunknown({m.sel_b1,m.sel_b2}) && {m.sel_b1,m.sel_b2}==2'b01});
  cover property (@(m.sel_b1 or m.sel_b2) {!$isunknown({m.sel_b1,m.sel_b2}) && {m.sel_b1,m.sel_b2}==2'b10});
  cover property (@(m.sel_b1 or m.sel_b2) {!$isunknown({m.sel_b1,m.sel_b2}) && {m.sel_b1,m.sel_b2}==2'b11});
endmodule


module top_module_sva (top_module t);
  default clocking cb @(posedge t.clk); endclocking
  bit past_valid;
  initial past_valid = 0;
  always @(posedge t.clk) past_valid <= 1;

  // Structural AND correctness
  assert property (t.out == (t.edge_detect_out & t.mux_out))
    else $error("top: out != edge_detect_out & mux_out");

  // When input changes, next-cycle out must be $past(in) AND current mux_out
  assert property (past_valid && (t.in !== $past(t.in)) |-> ##1
                   t.out == ($past(t.in) & t.mux_out))
    else $error("top: pipeline relation violated after input change");

  // Knownness after change (assuming valid selects handled in mux_sva)
  assert property (past_valid && (t.in !== $past(t.in)) |-> ##1 !$isunknown(t.out))
    else $error("top: out unknown after input change");

  // Coverage: exercise all mux selects at clock edges
  cover property ({t.sel_b1,t.sel_b2}==2'b00);
  cover property ({t.sel_b1,t.sel_b2}==2'b01);
  cover property ({t.sel_b1,t.sel_b2}==2'b10);
  cover property ({t.sel_b1,t.sel_b2}==2'b11);

  // Coverage: observe end-to-end update after an input change
  cover property (past_valid && (t.in !== $past(t.in)) ##1
                  (t.out == ($past(t.in) & t.mux_out)));
endmodule


// Bind the SVA modules to the DUTs
bind edge_detector edge_detector_sva ed_sva();
bind mux           mux_sva           mx_sva();
bind top_module    top_module_sva    top_sva();