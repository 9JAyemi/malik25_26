// SVA for the provided design. Bind these modules; no DUT changes required.

module transition_detector_sva (
  input clk, input reset,
  input [31:0] in,
  input [31:0] in_reg, in_reg_prev, in_xor,
  input out
);
  default clocking cb @(posedge clk); endclocking

  // Async reset takes effect immediately
  always @(posedge reset) begin
    assert (in_reg==32'd0 && in_reg_prev==32'd0 && in_xor==32'd0 && out==1'b0)
      else $error("transition_detector async reset values incorrect");
  end

  // While reset is asserted, hold at 0
  assert property (reset |-> (in_reg==0 && in_reg_prev==0 && in_xor==0 && out==0));

  // Pipelining and data movement (use past only when previous cycle was active)
  assert property ($past(!reset) |-> in_reg      == $past(in));
  assert property ($past(!reset) |-> in_reg_prev == $past(in_reg));
  assert property ($past(!reset) |-> in_xor      == ($past(in_reg) ^ $past(in_reg_prev)));

  // in_xor reflects two-cycle delta of input
  assert property ($past(!reset,2) |-> (in_xor!=0) == (($past(in,1) ^ $past(in,2)) != 0));

  // Out becomes 1 one cycle after in_xor!=0 and is sticky until reset
  assert property (disable iff (reset) (in_xor!=0) |=> out);
  assert property (disable iff (reset) $rose(out) |-> $past(in_xor!=0));
  assert property (disable iff (reset) out |=> out);

  // Coverage
  cover property (disable iff (reset) ($changed(in)) ##1 out);
  cover property (disable iff (reset) (out && $stable(in))[->3]); // out stays high while input stable
endmodule
bind transition_detector transition_detector_sva td_sva_i (.*);


// Bitwise combinational block checks (immediate, combinational)
module bitwise_operations_sva (
  input [2:0] a, b,
  input [2:0] out_and, out_xor, out_nor,
  input [2:0] a_not, b_not
);
  always @* begin
    assert (out_and == (a & b));
    assert (out_xor == (a ^ b));
    assert (out_nor == ~(a | b));
    assert (a_not  == ~a);
    assert (b_not  == ~b);
  end
  // Simple functional coverage
  logic _unused;
  always @* begin
    cover ((a==3'h0 && b==3'h7) || (a==3'h7 && b==3'h0) || (a==3'h5 && b==3'h2));
  end
endmodule
bind bitwise_operations bitwise_operations_sva bo_sva_i (.*);


// Functional module checks
module functional_module_sva (
  input clk, input reset,
  input transition_detect,
  input [2:0] bitwise_and,
  input [2:0] out_and
);
  default clocking cb @(posedge clk); endclocking

  assert property (reset |-> out_and==3'd0);

  // Update on detect with one-cycle latency, otherwise hold
  assert property (disable iff (reset) transition_detect |=> out_and == $past(bitwise_and));
  assert property (disable iff (reset) !transition_detect |=> out_and == $past(out_and));

  // Any change must be caused by prior detect
  assert property (disable iff (reset) $changed(out_and) |-> $past(transition_detect));

  // Coverage
  cover property (disable iff (reset) transition_detect ##1 (out_and == $past(bitwise_and)));
endmodule
bind functional_module functional_module_sva fm_sva_i (.*);


// Top-level integration checks
module top_module_sva (
  input clk, input reset,
  input [2:0] a, b,
  input [2:0] out_and_bitwise,
  input [5:0] out_not,
  input transition_detect,
  input [2:0] bitwise_and, bitwise_xor, bitwise_nor
);
  default clocking cb @(posedge clk); endclocking

  // out_not wiring and bitwise outputs seen at top
  assert property (out_not[2:0] == ~a && out_not[5:3] == ~b);
  assert property ((bitwise_and==(a&b)) && (bitwise_xor==(a^b)) && (bitwise_nor==~(a|b)));

  // Propagation from bitwise_and into out_and_bitwise via detect
  assert property (disable iff (reset) transition_detect |=> out_and_bitwise == $past(bitwise_and));
  assert property (disable iff (reset) !transition_detect |=> out_and_bitwise == $past(out_and_bitwise));

  // Integration coverage
  cover property (disable iff (reset)
                  $changed(a|b) ##1 transition_detect ##1 (out_and_bitwise == $past(bitwise_and)));
endmodule
bind top_module top_module_sva top_sva_i (.*);