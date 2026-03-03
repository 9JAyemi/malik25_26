// SVA for binary_counter
module binary_counter_sva(
  input clk,
  input reset,
  input [3:0] q
);
  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on key signals at sample and after update
  a_no_x_pre:  assert property ( !$isunknown({reset,q}) );
  a_no_x_post: assert property ( 1 |-> ##0 !$isunknown(q) );

  // Asynchronous reset must clear immediately
  a_async_clear: assert property ( @(posedge reset) ##0 (q == 4'h0) );

  // While reset is asserted, q must be 0 on every clock
  a_hold_zero_while_reset: assert property ( reset |-> (q == 4'h0) );

  // Next-state function (checked at every clk edge):
  // use $sampled(q) for pre-edge value and ##0 to see post-NBA q
  a_next_state: assert property (
    1 |-> ##0 ( q == ( reset ? 4'h0
                             : ( ($sampled(q) == 4'hF) ? 4'h0 : $sampled(q)+1 ) ) )
  );

  // Coverage
  c_async_reset: cover property ( @(posedge reset) ##0 (q == 4'h0) );
  c_inc:        cover property ( !reset && ($sampled(q) != 4'hF) ##0 (q == $sampled(q)+1) );
  c_wrap:       cover property ( !reset && ($sampled(q) == 4'hF) ##0 (q == 4'h0) );
  c_full_cycle: cover property ( (!reset)[*16] ##0 (q == $past(q,16)) );
endmodule

// Bind into the DUT
bind binary_counter binary_counter_sva bcsva(.clk(clk), .reset(reset), .q(q));