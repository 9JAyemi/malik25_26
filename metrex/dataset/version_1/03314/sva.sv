// SVA for counter
module counter_sva #(parameter W=4) (input clk, rst, input [W-1:0] count);
  default clocking @(posedge clk); endclocking

  // Basic safety
  a_count_known: assert property (!$isunknown(count));

  // Reset behavior: synchronous, forces zero
  a_rst_zero:   assert property (rst |-> count == '0);

  // Next-state function (mod-2^W increment) when not in reset
  a_next_fn:    assert property (disable iff (rst)
                      count == (($past(count)=={W{1'b1}}) ? '0
                                                            : $past(count)+1));

  // Coverage
  c_seen_reset:      cover property (rst);
  c_first_increment: cover property (rst ##1 !rst ##1 count == 'd1);
  c_wrap:            cover property (disable iff (rst)
                                     count == {W{1'b1}} ##1 count == '0);
  c_full_cycle:      cover property (disable iff (rst)
                                     count == '0 ##16 count == '0);
endmodule

// Bind into DUT
bind counter counter_sva #(.W(4)) counter_sva_i (.*);