// SVA checker for dff_async_reset_set
module dff_async_reset_set_sva (
  input clk,
  input reset_b,
  input set_b,
  input q,
  input reset_b_reg,
  input set_b_reg
);
  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // Synchronizer correctness
  a_sync_reset_capture: assert property (disable iff (!past_valid)
    reset_b_reg == $past(reset_b)
  );
  a_sync_set_capture: assert property (disable iff (!past_valid)
    set_b_reg == $past(set_b)
  );

  // No X/Z on key state after first valid cycle
  a_no_x: assert property (disable iff (!past_valid)
    !$isunknown({reset_b_reg, set_b_reg, q})
  );

  // Next-state function of q
  a_next_state: assert property (disable iff (!past_valid)
    q == ( $past(reset_b_reg) ? 1'b0 :
           $past(set_b_reg)  ? 1'b1 :
                               ~$past(q) )
  );

  // Reset dominates set when both were high in prior cycle
  a_reset_priority: assert property (disable iff (!past_valid)
    $past(reset_b_reg) && $past(set_b_reg) |-> q == 1'b0
  );

  // Coverage: exercise all behaviors
  c_reset:  cover property (past_valid && $past(reset_b_reg) && q == 1'b0);
  c_set:    cover property (past_valid && !$past(reset_b_reg) && $past(set_b_reg) && q == 1'b1);
  c_tog_01: cover property (past_valid && !$past(reset_b_reg) && !$past(set_b_reg) && !$past(q) &&  q);
  c_tog_10: cover property (past_valid && !$past(reset_b_reg) && !$past(set_b_reg) &&  $past(q) && !q);
  c_both:   cover property (past_valid && $past(reset_b_reg) && $past(set_b_reg) && q == 1'b0);
endmodule

// Bind into the DUT (connects to internals by name)
bind dff_async_reset_set dff_async_reset_set_sva u_dff_async_reset_set_sva (.*);