// SVA checker for twos_complement
module twos_complement_sva
(
  input logic        clk,
  input logic        rst,         // async, active-high
  input logic [3:0]  in,
  input logic [7:0]  out,
  input logic [3:0]  in_reg,      // internal
  input logic        valid        // internal
);

  default clocking cb @(posedge clk); endclocking

  // Async reset clears immediately on rst posedge
  a_async_reset_clears: assert property (@(posedge rst) ##0 (in_reg==4'd0 && valid==1'b0 && out==8'd0));

  // While rst is held, state is cleared on each clk
  a_reset_holds_clear: assert property (rst |=> (in_reg==4'd0 && valid==1'b0 && out==8'd0));

  // valid sets on first post-deassertion clock, then sticks high
  a_valid_sets_after_reset: assert property ($fell(rst) |=> valid);
  a_valid_sticky:           assert property (disable iff (rst) valid |=> valid);

  // in_reg tracks previous-cycle input
  a_inreg_tracks_in: assert property (disable iff (rst) in_reg == $past(in));

  // Functional update: when input is stable and valid, out updates to (prev in + 1); otherwise holds
  a_update_value:        assert property (disable iff (rst) (valid && (in == $past(in))) |=> out == ({4'b0,$past(in)} + 8'd1));
  a_hold_when_no_update: assert property (disable iff (rst) !(valid && (in == $past(in))) |=> out == $past(out));

  // Output stays within reachable range [0..16] after reset
  a_out_range: assert property (disable iff (rst) out <= 8'd16);

  // No X/Z after reset
  a_no_unknowns: assert property (disable iff (rst) !$isunknown({in, out, in_reg, valid}));

  // Coverage
  c_reset_then_valid:        cover property ($fell(rst) |=> valid);
  c_update_at_zero:          cover property (disable iff (rst) (valid && in==$past(in) && in==4'd0)  |=> out==8'd1);
  c_update_at_max:           cover property (disable iff (rst) (valid && in==$past(in) && in==4'd15) |=> out==8'd16);
  c_change_breaks_update:    cover property (disable iff (rst) valid && $changed(in) |=> out==$past(out));
  c_two_consecutive_updates: cover property (disable iff (rst) (valid && in==$past(in)) [*2]);

endmodule

// Bind into DUT (accesses internal in_reg and valid)
bind twos_complement twos_complement_sva u_twos_complement_sva
(
  .clk   (clk),
  .rst   (rst),
  .in    (in),
  .out   (out),
  .in_reg(in_reg),
  .valid (valid)
);