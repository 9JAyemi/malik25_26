// SVA for the given design. Bind these to the RTL (no DUT edits needed).

// Barrel shifter (actually pass-through)
module barrel_shifter_sva(input [7:0] in, input [7:0] out);
  // Combinational equivalence
  assert property (@(*)) (out == in);
endmodule
bind barrel_shifter barrel_shifter_sva bs_sva_i(.in(in), .out(out));

// Bitwise OR
module bitwise_or_sva(input [31:0] in1, input [31:0] in2, input [31:0] out);
  // Combinational equivalence
  assert property (@(*)) (out == (in1 | in2));
endmodule
bind bitwise_or bitwise_or_sva bo_sva_i(.in1(in1), .in2(in2), .out(out));

// Rising edge detector
module rising_edge_detector_sva(
  input clk, input reset,
  input [31:0] in32, input [31:0] out,
  input [31:0] prev_in, input [31:0] rising_edge_mask
);
  // Async reset drives all zeros immediately
  assert property (@(posedge reset)) (prev_in==32'b0 && rising_edge_mask==32'b0 && out==32'b0);

  // While reset held, state stays zero
  assert property (@(posedge clk) reset |-> ##0 (prev_in==32'b0 && rising_edge_mask==32'b0 && out==32'b0));

  // Next-state relations (use ##0 to observe post-NBA updated values)
  assert property (@(posedge clk) disable iff (reset) ##0 (prev_in == in32));
  assert property (@(posedge clk) disable iff (reset) ##0 (rising_edge_mask == ((in32 ^ $past(prev_in)) & in32)));
  assert property (@(posedge clk) disable iff (reset) ##0 (out == ($past(out) | ((in32 ^ $past(prev_in)) & in32))));

  // Sticky-out: no 1->0 transitions without reset
  assert property (@(posedge clk) disable iff (reset) ##0 (($past(out) & ~out) == 32'b0));

  // Any rising input bit must set corresponding out bit that cycle
  assert property (@(posedge clk) disable iff (reset) ##0 (((in32 & ~ $past(in32)) & ~out) == 32'b0));

  // Coverage: observe at least one new set bit due to a rising edge
  cover property (@(posedge clk) disable iff (reset)
                  ((in32 & ~ $past(in32)) != 32'b0) ##0 ((out & ~ $past(out)) != 32'b0));
  // Coverage: eventually accumulate all ones
  cover property (@(posedge clk) disable iff (reset) out == 32'hFFFF_FFFF);
endmodule
bind rising_edge_detector rising_edge_detector_sva red_sva_i(
  .clk(clk), .reset(reset), .in32(in32), .out(out),
  .prev_in(prev_in), .rising_edge_mask(rising_edge_mask)
);

// Top-level integration checks
module top_module_sva(
  input clk, input reset,
  input [7:0] in,
  input [7:0] reversed_in,
  input [31:0] rising_edge_out,
  input [31:0] out
);
  // Structural equivalence of OR result
  assert property (@(*)) (out == (rising_edge_out | {24'b0, reversed_in}));

  // Lower byte comes from 'in' when rising_edge_out[7:0]==0
  assert property (@(posedge clk)) ((rising_edge_out[7:0]==8'b0) |-> (out[7:0] == in));

  // Upper 24 bits come solely from rising_edge_out
  assert property (@(posedge clk)) (out[31:8] == rising_edge_out[31:8]);

  // Coverage: lower byte pass-through
  cover property (@(posedge clk) (rising_edge_out[7:0]==8'b0 && in!=8'b0 && out[7:0]==in));
  // Coverage: overlapping contribution on bit 0
  cover property (@(posedge clk) ((rising_edge_out[0]==1'b1) && (in[0]==1'b1) && (out[0]==1'b1)));
endmodule
bind top_module top_module_sva top_sva_i(
  .clk(clk), .reset(reset), .in(in),
  .reversed_in(reversed_in), .rising_edge_out(rising_edge_out), .out(out)
);