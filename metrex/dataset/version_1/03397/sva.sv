// SVA for top_module and submodules. Focused, high-signal-coverage, and concise.

// dual_edge_ff: q is d delayed by 2 cycles once out of reset; q==0 in reset; no X on q.
module dual_edge_ff_sva (input clk, input reset, input [31:0] d, input [31:0] q);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset);

  // After two clean cycles out of reset, q must equal d delayed by 2
  assert property (reset && $past(reset) && $past(reset,2) |-> q == $past(d,2))
    else $error("dual_edge_ff: q != $past(d,2)");

  // In reset, q must be 0 at each clock
  assert property (@(posedge clk) !reset |-> q == 32'h0)
    else $error("dual_edge_ff: q not 0 during reset");

  // No X/Z on q out of reset
  assert property (!$isunknown(q))
    else $error("dual_edge_ff: q is X/Z");
endmodule
bind dual_edge_ff dual_edge_ff_sva dff_sva (.*);

// rising_edge_detector: out == in & ~ $past(out); out==0 in reset and when in==0; no X on out.
module rising_edge_detector_sva (input clk, input reset, input [31:0] in, input [31:0] out);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset);

  // Avoid first-cycle-after-reset $past issue by requiring a valid past
  assert property ($past(reset) |-> out == (in & ~ $past(out)))
    else $error("rising_edge_detector: out != (in & ~ $past(out))");

  // When in==0, out must be 0 next cycle
  assert property (in == 32'h0 |-> out == 32'h0)
    else $error("rising_edge_detector: out not 0 when in==0");

  // In reset, out must be 0
  assert property (@(posedge clk) !reset |-> out == 32'h0)
    else $error("rising_edge_detector: out not 0 during reset");

  // No X/Z on out out of reset
  assert property (!$isunknown(out))
    else $error("rising_edge_detector: out is X/Z");
endmodule
bind rising_edge_detector rising_edge_detector_sva red_sva (.*);

// xor_functional: pure combinational XOR equivalence (4-state)
module xor_functional_sva (input [31:0] in1, input [31:0] in2, input [31:0] out);
  always_comb begin
    assert (out === (in1 ^ in2))
      else $error("xor_functional: out != in1 ^ in2");
  end
endmodule
bind xor_functional xor_functional_sva xor_sva (.*);

// top_module: mux correctness, reset behavior, X checks, and key coverage.
module top_module_sva (
  input clk,
  input reset,
  input [31:0] in,
  input [1:0]  select,
  input [31:0] ff_out,
  input [31:0] red_out,
  input [31:0] out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset);

  // Mux function (note: xor_out == ff_out ^ red_out)
  assert property (
    out == ((select==2'b00) ? ff_out :
            (select==2'b01) ? red_out :
            (select==2'b10) ? (ff_out ^ red_out) :
                              32'h0)
  ) else $error("top: mux mapping violated");

  // In reset, all observable outputs are 0
  assert property (@(posedge clk) !reset |-> (ff_out==32'h0 && red_out==32'h0 && out==32'h0))
    else $error("top: outputs not 0 during reset");

  // No X/Z on control/outputs out of reset
  assert property (!$isunknown({select, ff_out, red_out, out}))
    else $error("top: X/Z on select/outputs");

  // Sanity: select==2'b11 forces out==0; select==2'b10 is XOR path
  assert property ((select==2'b11) |-> out==32'h0)
    else $error("top: select==11 not zeroing out");
  assert property ((select==2'b10) |-> out==(ff_out ^ red_out))
    else $error("top: select==10 not XOR");

  // Coverage
  cover property ($fell(reset));
  cover property ($rose(reset));
  cover property (select==2'b00);
  cover property (select==2'b01);
  cover property (select==2'b10);
  cover property (select==2'b11);

  // Observe dff latency effect through mux 00
  cover property (select==2'b00 && reset && $past(reset,2) && out == $past(in,2));

  // Observe red_out toggling (use LSB to keep it light) when selected
  cover property (select==2'b01 && $past(reset) && in[0] && $past(in[0]) && out[0] != $past(out[0]));

  // Observe XOR path active with nontrivial operands
  cover property (select==2'b10 && (ff_out ^ red_out) != 32'h0 && out == (ff_out ^ red_out));
endmodule
bind top_module top_module_sva top_sva (
  .clk(clk),
  .reset(reset),
  .in(in),
  .select(select),
  .ff_out(ff_out),
  .red_out(red_out),
  .out(out)
);