// SVA for DLL. Bind this checker to the DUT instance.
// Example:
// bind DLL DLL_sva u_dll_sva(
//   .ref_clk(ref_clk), .feedback_clk(feedback_clk), .delay(delay), .out_clk(out_clk),
//   .delay_reg(delay_reg), .delay_next(delay_next),
//   .error(error), .error_filtered(error_filtered), .error_integrated(error_integrated),
//   .error_integrated_next(error_integrated_next), .error_filtered_next(error_filtered_next),
//   .phase_detector_out(phase_detector_out), .delay_line_out(delay_line_out),
//   .out_clk_reg(out_clk_reg), .out_clk_next(out_clk_next)
// );

module DLL_sva (
  input  logic        ref_clk,
  input  logic        feedback_clk,
  input  logic [7:0]  delay,
  input  logic        out_clk,

  input  logic [7:0]  delay_reg,
  input  logic [7:0]  delay_next,
  input  logic [7:0]  error,
  input  logic [7:0]  error_filtered,
  input  logic [7:0]  error_integrated,
  input  logic [7:0]  error_integrated_next,
  input  logic [7:0]  error_filtered_next,
  input  logic [7:0]  phase_detector_out,
  input  logic [7:0]  delay_line_out,
  input  logic [7:0]  out_clk_reg,
  input  logic [7:0]  out_clk_next
);

  // Enable flags to avoid first-cycle $past issues
  bit ref_seen, fb_seen;
  always @(posedge ref_clk) ref_seen <= 1'b1;
  always @(posedge feedback_clk) fb_seen <= 1'b1;

  // out_clk is the LSB of out_clk_reg (assignment truncates)
  assert property (@(posedge ref_clk) out_clk === out_clk_reg[0]);
  assert property (@(posedge feedback_clk) out_clk === out_clk_reg[0]);

  // Ref clocked register-moves (check one-cycle-late to observe NBA updates)
  assert property (@(posedge ref_clk) disable iff (!ref_seen)
                   $past(delay_reg)           == $past(delay, 1, ref_clk));
  assert property (@(posedge ref_clk) disable iff (!ref_seen)
                   $past(delay_next)          == $past(delay_reg, 1, ref_clk));
  assert property (@(posedge ref_clk) disable iff (!ref_seen)
                   $past(error)               == $past(phase_detector_out, 1, ref_clk));
  assert property (@(posedge ref_clk) disable iff (!ref_seen)
                   $past(error_filtered)      == $past(error_filtered_next, 1, ref_clk));
  assert property (@(posedge ref_clk) disable iff (!ref_seen)
                   $past(error_integrated)    == $past(error_integrated_next, 1, ref_clk));
  assert property (@(posedge ref_clk) disable iff (!ref_seen)
                   $past(out_clk_reg)         == $past(out_clk_next, 1, ref_clk));

  // Feedback clocked computations
  // Delay line "hold/load" behavior (last nonblocking assignment wins, controlled by delay_reg[0])
  assert property (@(posedge feedback_clk) disable iff (!fb_seen)
                   $past(delay_reg[0], 1, feedback_clk) |-> (delay_line_out == $past(delay_line_out, 1, feedback_clk)));
  assert property (@(posedge feedback_clk) disable iff (!fb_seen)
                   !$past(delay_reg[0], 1, feedback_clk) |-> (delay_line_out[0] == 1'b1 && delay_line_out[7:1] == '0));

  // Phase detector (XOR with 8'b0000_0001: LSB toggles, upper bits pass-through)
  assert property (@(posedge feedback_clk) disable iff (!fb_seen)
                   phase_detector_out[0]   == ($past(delay_line_out[0], 1, feedback_clk) ^ 1'b1));
  assert property (@(posedge feedback_clk) disable iff (!fb_seen)
                   phase_detector_out[7:1] ==  $past(delay_line_out[7:1], 1, feedback_clk));

  // Filter and integrator math
  assert property (@(posedge feedback_clk) disable iff (!fb_seen)
                   error_filtered_next == (($past(error_filtered, 1, feedback_clk) + $past(error, 1, feedback_clk)) >> 1));
  assert property (@(posedge feedback_clk) disable iff (!fb_seen)
                   error_integrated_next == ($past(error_integrated, 1, feedback_clk) + $past(error_filtered_next, 1, feedback_clk)));

  // Delay update computation (note: design never applies delay_next to delay_reg; this checks the expression as coded)
  assert property (@(posedge feedback_clk) disable iff (!fb_seen)
                   delay_next == ($past(delay_reg, 1, feedback_clk) + $past(error_integrated_next, 1, feedback_clk)));

  // out_clk_next selection (last nonblocking assignment wins, controlled by delay_reg[0])
  assert property (@(posedge feedback_clk) disable iff (!fb_seen)
                   $past(delay_reg[0], 1, feedback_clk) |-> (out_clk_next == $past(out_clk_reg, 1, feedback_clk)));
  assert property (@(posedge feedback_clk) disable iff (!fb_seen)
                   !$past(delay_reg[0], 1, feedback_clk) |-> (out_clk_next == $past(delay_line_out, 1, feedback_clk)));

  // Sanity: no X on primary clocks/outputs at sampling points
  assert property (@(posedge ref_clk) !$isunknown(ref_clk) && !$isunknown(out_clk));
  assert property (@(posedge feedback_clk) !$isunknown(feedback_clk));

  // -----------------
  // Functional coverage
  // -----------------
  // Exercise both MUX paths for delay_line_out and out_clk_next
  cover property (@(posedge feedback_clk) disable iff (!fb_seen) $past(delay_reg[0], 1, feedback_clk));
  cover property (@(posedge feedback_clk) disable iff (!fb_seen) !$past(delay_reg[0], 1, feedback_clk));
  cover property (@(posedge feedback_clk) disable iff (!fb_seen)
                  !$past(delay_reg[0],1,feedback_clk) && (out_clk_next == $past(delay_line_out,1,feedback_clk)));
  cover property (@(posedge feedback_clk) disable iff (!fb_seen)
                  $past(delay_reg[0],1,feedback_clk)  && (out_clk_next == $past(out_clk_reg,1,feedback_clk)));

  // Phase detector LSB hits both 0 and 1
  cover property (@(posedge feedback_clk) phase_detector_out[0] == 1'b0);
  cover property (@(posedge feedback_clk) phase_detector_out[0] == 1'b1);

  // Filter/integrator activity
  cover property (@(posedge feedback_clk) error_filtered_next != 8'h00);
  cover property (@(posedge feedback_clk) error_integrated_next != 8'h00);
  // Wrap-around indication (optional)
  cover property (@(posedge feedback_clk) error_integrated_next < $past(error_integrated, 1, feedback_clk));

  // out_clk changes (only on ref_clk)
  cover property (@(posedge ref_clk) $changed(out_clk));

endmodule