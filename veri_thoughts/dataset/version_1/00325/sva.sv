// SVA for up_counter
module up_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  count,
  input logic        out
);
  default clocking cb @(posedge clk); endclocking

  // Synchronous reset drives zeros (visible next sample)
  a_reset_next: assert property (reset |=> (count == 4'h0 && out == 1'b0));

  // Free-run behavior: modulo-16 increment and out toggles each non-reset cycle
  a_next_update: assert property (
    !reset |=> (
      ( ($past(count) == 4'hF) ? (count == 4'h0) : (count == $past(count) + 4'h1) )
      && (out == ~ $past(out))
    )
  );

  // No X/Z when not in reset
  a_no_x: assert property (!reset |-> !($isunknown(count) || $isunknown(out)));

  // Coverage
  c_wrap:      cover property (!reset && $past(!reset) && $past(count) == 4'hF && count == 4'h0);
  c_toggle:    cover property (!reset && $past(!reset) && (out == ~ $past(out)));
  c_16_cycle:  cover property ((!reset)[*16] ##1 (count == $past(count,16) && out == $past(out,16)));
  c_rst_rise:  cover property ($rose(reset));
  c_rst_fall:  cover property ($fell(reset));
endmodule

// Bind to DUT
bind up_counter up_counter_sva u_up_counter_sva (.clk(clk), .reset(reset), .count(count), .out(out));