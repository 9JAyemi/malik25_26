// SVA for binary_counter
module binary_counter_sva (
  input logic        clk,
  input logic        rst,
  input logic [3:0]  count,
  input logic        max_count_reached
);

  default clocking cb @(posedge clk); endclocking

  // Synchronous reset drives zeros
  a_reset: assert property (rst |-> (count==4'h0 && max_count_reached==1'b0));

  // Disable checks while in reset
  default disable iff (rst);

  // No X/Z on outputs out of reset
  a_known: assert property (!$isunknown({count, max_count_reached}));

  // Next-state: modulo-16 increment; wrap flags exactly on wrap
  a_next_state_mod16: assert property (
    !$past(rst) |-> (count == (($past(count)+1) & 4'hF)) &&
                    (max_count_reached == ($past(count)==4'hF))
  );

  // First cycle after reset deassertion: 0 -> 1, no flag
  a_first_out_of_reset: assert property (
    $fell(rst) |-> (count==4'h1 && !max_count_reached)
  );

  // Flag is a one-cycle pulse and coincides with count==0
  a_flag_implies_zero: assert property (max_count_reached |-> count==4'h0);
  a_flag_one_pulse:    assert property (max_count_reached |-> ##1 !max_count_reached);

  // Coverage
  c_wrap: cover property (!$past(rst) && $past(count)==4'hF && count==4'h0 && max_count_reached);
  c_pulse: cover property (max_count_reached ##1 !max_count_reached);
  c_full_cycle: cover property (
    rst ##1 !rst
    ##1 (count==4'h1) ##1 (count==4'h2) ##1 (count==4'h3) ##1 (count==4'h4)
    ##1 (count==4'h5) ##1 (count==4'h6) ##1 (count==4'h7) ##1 (count==4'h8)
    ##1 (count==4'h9) ##1 (count==4'hA) ##1 (count==4'hB) ##1 (count==4'hC)
    ##1 (count==4'hD) ##1 (count==4'hE) ##1 (count==4'hF) ##1 (count==4'h0 && max_count_reached)
  );

endmodule

// Bind into DUT
bind binary_counter binary_counter_sva u_binary_counter_sva (
  .clk(clk),
  .rst(rst),
  .count(count),
  .max_count_reached(max_count_reached)
);