// SVA for schmitt_trigger
// Bindable, concise, checks functionality and covers key behaviors

module schmitt_trigger_sva (
  input logic in,
  input logic Vt_high,
  input logic Vt_low,
  input logic Vdd,
  input logic out,
  input logic out_reg,
  input logic prev_out_reg
);

  // Default clock for sampled checks (uses Vdd posedge as the design’s sampling event)
  default clocking cb @(posedge Vdd); endclocking

  // Sanity: no X/Z on key pins
  assert property (@(in or Vt_high or Vt_low or out or prev_out_reg or Vdd)
                   !$isunknown({in,Vt_high,Vt_low,out,prev_out_reg}));

  // Threshold ordering (for a valid Schmitt configuration)
  assert property (cb (Vt_high >= Vt_low));

  // Out is just a wire to out_reg
  assert property (@(out or out_reg) out == out_reg);

  // Combinational function is exactly as coded (checked on any relevant change)
  assert property (@(in or prev_out_reg or Vt_high or Vt_low)
                   (prev_out_reg == 1'b0) |-> (out == (in >= Vt_high)));
  assert property (@(in or prev_out_reg or Vt_high or Vt_low)
                   (prev_out_reg == 1'b1) |-> (out == !(in <= Vt_low)));

  // Legal transitions only: rising requires high-threshold, falling requires low-threshold
  assert property (@(posedge out) (!prev_out_reg && (in >= Vt_high)));
  assert property (@(negedge out) ( prev_out_reg && (in <= Vt_low)));

  // prev_out_reg captures current out at each Vdd posedge (checked next cycle)
  assert property (cb 1 |=> (prev_out_reg == $past(out)));

  // Coverage: observe both directions and a full hysteresis cycle across samples
  cover property (@(posedge out) 1);
  cover property (@(negedge out) 1);
  cover property (cb (!prev_out_reg && (in >= Vt_high)) ##[1:$] (prev_out_reg && (in <= Vt_low)));

endmodule

// Bind into DUT
bind schmitt_trigger schmitt_trigger_sva sva (
  .in(in),
  .Vt_high(Vt_high),
  .Vt_low(Vt_low),
  .Vdd(Vdd),
  .out(out),
  .out_reg(out_reg),
  .prev_out_reg(prev_out_reg)
);