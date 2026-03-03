// SVA for debounce module
// Quality-focused, concise, with both black-box and white-box (internal) checks.
// Bind examples at bottom.

// Black-box checker (no internal signals required)
module debounce_sva_bb(input logic clk,
                       input logic pb,
                       input logic pb_debounced);

  default clocking cb @ (posedge clk); endclocking

  // Enable assertions only after 4 samples so $past depths are valid and shift window is filled
  logic [2:0] samp_cnt;
  always_ff @(posedge clk) if (samp_cnt != 3'd4) samp_cnt <= samp_cnt + 3'd1;
  wire past4_ready = (samp_cnt == 3'd4);

  // Output equals OR of current+last 3 samples of pb (functional spec)
  property p_or_window;
    pb_debounced == (pb || $past(pb,1) || $past(pb,2) || $past(pb,3));
  endproperty
  a_or_window: assert property (disable iff (!past4_ready) p_or_window);

  // Deassert exactly when 4 consecutive zeros are seen
  a_fall_after_4_zeros: assert property (disable iff (!past4_ready)
                                         (!pb[*4]) |=> !pb_debounced);

  // Zero-latency rise: if output was 0 and pb is 1 this cycle, output rises this cycle
  a_rise_zero_latency: assert property (disable iff (!past4_ready)
                                        (!$past(pb_debounced) && pb) |-> pb_debounced);

  // No X on output once window is valid
  a_no_x_out: assert property (disable iff (!past4_ready) !$isunknown(pb_debounced));

  // Coverage
  c_rise: cover property (past4_ready && $rose(pb_debounced));
  c_fall_after_4_zeros: cover property (past4_ready && pb_debounced ##1 !pb[*4] ##1 $fell(pb_debounced));
  c_stuck_low: cover property (past4_ready && !pb[*5] ##1 !pb_debounced);

endmodule


// White-box checker (uses internal shift_reg)
module debounce_sva_wb(input  logic       clk,
                       input  logic       pb,
                       input  logic       pb_debounced,
                       input  logic [3:0] shift_reg);

  default clocking cb @ (posedge clk); endclocking

  // After first cycle, shift behavior must hold exactly
  a_shift: assert property (shift_reg == { $past(shift_reg[2:0]), $past(pb) });

  // Output equals reduction-OR of shift_reg
  a_map_out: assert property (pb_debounced == (shift_reg != 4'b0000));

  // Coverage: drain to zero after 4 zeros
  c_drain: cover property (pb_debounced ##1 !pb[*4] ##1 (shift_reg == 4'b0000) && !pb_debounced);

endmodule


// Example binds (uncomment as needed):
// bind debounce debounce_sva_bb u_debounce_sva_bb(.clk(clk), .pb(pb), .pb_debounced(pb_debounced));
// bind debounce debounce_sva_wb u_debounce_sva_wb(.clk(clk), .pb(pb), .pb_debounced(pb_debounced), .shift_reg(shift_reg));