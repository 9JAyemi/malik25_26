// SVA for binary_counter
module binary_counter_sva(input logic clk, rst, input logic [3:0] count);

  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on key signals
  ap_no_x: assert property (!$isunknown({rst, count})) else $error("X/Z on rst/count");

  // Reset behavior: cycle after rst=1, count must be 0
  ap_rst_to_zero: assert property ($past(rst) |-> (count == 4'h0));

  // Next-state function when not in reset
  ap_next_state: assert property (
    !$past(rst) |-> (count == (($past(count) == 4'hF) ? 4'h0 : ($past(count) + 1)))
  );

  // Coverage
  cv_reset_seen: cover property (rst);
  cv_wrap:       cover property (!$past(rst) && ($past(count) == 4'hF) ##1 (count == 4'h0));
  cv_full_cycle: cover property (
    !rst && (count == 4'h0)
    ##1 (!rst && (count == $past(count)+1))[*15]
    ##1 (!rst && (count == 4'h0))
  );

endmodule

// Bind into DUT
bind binary_counter binary_counter_sva u_binary_counter_sva(.clk(clk), .rst(rst), .count(count));