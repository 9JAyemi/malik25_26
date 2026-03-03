// SVA for edge_detector: concise, high-quality checks and coverage
module edge_detector_sva #(parameter int W=8) (
  input logic                 clk,
  input logic [W-1:0]         in,
  input logic [W-1:0]         anyedge,
  input logic [W-1:0]         prev_in,
  input logic [2:0]           count
);

  default clocking cb @(posedge clk); endclocking
  // Disable checks while any relevant signal is X (covers init/no-reset phase)
  default disable iff ($isunknown({in, anyedge, prev_in, count}));

  let changed = (in != $past(in));

  // prev_in must capture prior in
  ap_prev_in_mirror: assert property (prev_in == $past(in));

  // anyedge is a shift register with LSB = "any edge" flag
  ap_shift_and_insert: assert property (
    anyedge == {$past(anyedge[W-2:0]), changed}
  );

  // Count must increment modulo-8 every cycle
  ap_count_increments: assert property (count == $past(count) + 3'd1);

  // Sanity: "any edge" equals reduction of bitwise XOR
  ap_changed_equiv: assert property (changed == (|(in ^ $past(in))));

  // Coverage: observe both edge and no-edge, back-to-back edges, quiet then edge
  cp_edge:         cover property (changed);
  cp_no_edge:      cover property (!changed);
  cp_2_edges:      cover property (changed ##1 changed);
  cp_quiet_then_e: cover property (!changed[*3] ##1 changed);

endmodule

// Bind SVA to DUT
bind edge_detector edge_detector_sva #(.W(8)) edge_detector_sva_b (
  .clk(clk),
  .in(in),
  .anyedge(anyedge),
  .prev_in(prev_in),
  .count(count)
);