// SVA for shift_register
// Bindable checker that verifies functional correctness and provides concise coverage

module shift_register_sva (
    input  logic        clk,
    input  logic        load,
    input  logic [3:0]  in,
    input  logic [3:0]  out,
    input  logic [3:0]  out_next,
    // internal state taps
    input  logic [3:0]  stage1,
    input  logic [3:0]  stage2,
    input  logic [3:0]  stage3,
    input  logic [3:0]  stage4
);

  // past-valid tracking
  logic pv1;
  always_ff @(posedge clk) pv1 <= 1'b1;

  // Combinational tie-offs must hold at all times (sampled on clk)
  assert property (@(posedge clk) out      == stage1);
  assert property (@(posedge clk) out_next == stage2);

  // One-cycle state updates (guard $past usage)
  assert property (@(posedge clk) pv1 |-> stage1 == ($past(load) ? $past(in)     : $past(stage2)));
  assert property (@(posedge clk) pv1 |-> stage2 == $past(stage3));
  assert property (@(posedge clk) pv1 |-> stage3 == $past(stage4));
  assert property (@(posedge clk) pv1 |-> stage4 == $past(stage2)); // via out_next

  // Output sequencing relative to prior cycle
  assert property (@(posedge clk) pv1 &&  $past(load)  |-> out == $past(in));
  assert property (@(posedge clk) pv1 && !$past(load)  |-> out == $past(out_next));

  // 3-cycle rotation of the {stage2,stage3,stage4} ring
  assert property (@(posedge clk) pv1 && $past(pv1,2) |-> stage2 == $past(stage2,3));

  // Basic X-check on observable outputs after first edge
  assert property (@(posedge clk) pv1 |-> !$isunknown({out, out_next}));

  // Coverage
  cover property (@(posedge clk) pv1 &&  load);                       // exercise load path
  cover property (@(posedge clk) pv1 && !load);                       // exercise shift path
  cover property (@(posedge clk) pv1 &&  $past(load)  && out == $past(in));
  cover property (@(posedge clk) pv1 && !$past(load)  && out == $past(out_next));
  cover property (@(posedge clk) pv1 && $past(pv1,2) && stage2 == $past(stage2,3)); // observe ring rotation

endmodule

// Bind into the DUT
bind shift_register shift_register_sva sva_i (
  .clk(clk),
  .load(load),
  .in(in),
  .out(out),
  .out_next(out_next),
  .stage1(stage1),
  .stage2(stage2),
  .stage3(stage3),
  .stage4(stage4)
);