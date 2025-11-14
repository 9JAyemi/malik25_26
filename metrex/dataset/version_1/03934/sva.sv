// SVA for top_module and submodules. Focused, high-signal-coverage, concise.

////////////////////////////////////////////////////////////
// Assertions bound into edge_detector (generic per instance)
module edge_detector_sva (input clk, input [7:0] in, input out);
  bit init;
  initial init = 0;
  always @(posedge clk) init <= 1;

  // out must reflect whether in changed since previous clk
  assert property (@(posedge clk) disable iff (!init)
                   out == (in != $past(in)));

  // Simple safety: no X after first sampled cycle
  assert property (@(posedge clk) disable iff (!init)
                   !$isunknown(out));

  // Minimal functional coverage
  cover property (@(posedge clk) disable iff (!init) $changed(in) && out);
  cover property (@(posedge clk) disable iff (!init) $stable(in)  && !out);
endmodule
bind edge_detector edge_detector_sva u_edge_detector_sva(.clk(clk), .in(in), .out(out));

////////////////////////////////////////////////////////////
// Assertions bound into top_module to check composition/glue
module top_module_sva (
  input clk,
  input [15:0] in,
  input [7:0]  upper_byte,
  input [7:0]  lower_byte,
  input        upper_edge,
  input        lower_edge,
  input        anyedge
);
  bit init;
  initial init = 0;
  always @(posedge clk) init <= 1;

  // Byte splitter must split exactly
  assert property (@(posedge clk) {upper_byte, lower_byte} == in);

  // OR combine must be exact
  assert property (@(posedge clk) anyedge == (upper_edge | lower_edge));

  // Each edge flag must correspond to byte changes; anyedge must reflect any byte change
  assert property (@(posedge clk) disable iff (!init)
                   upper_edge == $changed(upper_byte));
  assert property (@(posedge clk) disable iff (!init)
                   lower_edge == $changed(lower_byte));
  assert property (@(posedge clk) disable iff (!init)
                   anyedge == ($changed(upper_byte) || $changed(lower_byte)));

  // No X on primary edge signals after first sample
  assert property (@(posedge clk) disable iff (!init)
                   !$isunknown({upper_edge, lower_edge, anyedge}));

  // Minimal cross-coverage of edge scenarios
  cover property (@(posedge clk) disable iff (!init)
                  $changed(upper_byte) && !$changed(lower_byte) && upper_edge && !lower_edge && anyedge);
  cover property (@(posedge clk) disable iff (!init)
                  !$changed(upper_byte) && $changed(lower_byte) && !upper_edge && lower_edge && anyedge);
  cover property (@(posedge clk) disable iff (!init)
                  $changed(upper_byte) && $changed(lower_byte) && upper_edge && lower_edge && anyedge);
  cover property (@(posedge clk) disable iff (!init)
                  !$changed(upper_byte) && !$changed(lower_byte) && !upper_edge && !lower_edge && !anyedge);
endmodule
bind top_module top_module_sva u_top_module_sva(
  .clk(clk),
  .in(in),
  .upper_byte(upper_byte),
  .lower_byte(lower_byte),
  .upper_edge(upper_edge),
  .lower_edge(lower_edge),
  .anyedge(anyedge)
);