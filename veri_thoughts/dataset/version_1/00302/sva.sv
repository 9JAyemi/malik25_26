// SVA checker for counter
module counter_sva (
  input logic       clk,
  input logic       rst,
  input logic [3:0] count
);
  default clocking @(posedge clk); endclocking

  // past-valid guard for $past
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // X/Z checks
  a_known:            assert property (!$isunknown({rst, count}));

  // Synchronous reset forces zero in the same cycle
  a_rst_zero:         assert property (rst |-> count == 4'd0);

  // Increment by exactly 1 each cycle when not in reset (wraps naturally in 4 bits)
  a_inc_no_rst:       assert property (disable iff (!past_valid || rst)
                                       count == $past(count) + 4'd1);

  // First cycle after deasserting reset must go to 1
  a_postreset_one:    assert property ($past(rst) && !rst |-> count == 4'd1);

  // Explicit wrap check F -> 0 when not in reset
  a_wrap:             assert property (disable iff (rst || !past_valid)
                                       ($past(count) == 4'hF) |-> (count == 4'h0));

  // Coverage
  c_seen_reset:       cover property (rst);
  c_postreset_one:    cover property ($past(rst) && !rst && count == 4'd1);
  c_wrap:             cover property (disable iff (rst || !past_valid)
                                       $past(count) == 4'hF && count == 4'h0);
  c_midstream_reset:  cover property (!rst && count != 4'd0 ##1 rst ##1 !rst && count == 4'd1);
endmodule

// Bind into DUT
bind counter counter_sva u_counter_sva (.clk(clk), .rst(rst), .count(count));