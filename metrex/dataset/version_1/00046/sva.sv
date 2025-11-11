// SVA for up_down_counter
module up_down_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic        up_down,
  input logic [2:0]  count
);

  default clocking cb @(posedge clk); endclocking

  // No X/Z on key signals
  ap_no_x_ctrl:  assert property ( !$isunknown({reset, up_down}) );
  ap_no_x_count: assert property ( !$isunknown(count) );

  // Synchronous reset behavior
  ap_reset_zero: assert property ( reset |-> count == 3'd0 );

  // Next-state functional check
  function automatic logic [2:0] next_cnt (bit up, logic [2:0] c);
    return up ? ((c==3'd7) ? 3'd0 : c+3'd1)
              : ((c==3'd0) ? 3'd7 : c-3'd1);
  endfunction

  ap_next_state: assert property ( disable iff (reset)
    !$isunknown($past({up_down,count},1,reset))
    |-> count == next_cnt($past(up_down,1,reset), $past(count,1,reset))
  );

  // Optional: ensure the counter moves every active cycle
  ap_moves: assert property ( disable iff (reset)
    !$isunknown($past(count,1,reset)) |-> count != $past(count,1,reset)
  );

  // Coverage: reset, inc/dec and both wraps
  cv_reset:     cover property ( reset && count==3'd0 );

  cv_inc:       cover property ( disable iff (reset)
    $past(up_down,1,reset) && ($past(count,1,reset)!=3'd7) &&
    count == ($past(count,1,reset)+3'd1)
  );

  cv_dec:       cover property ( disable iff (reset)
    !$past(up_down,1,reset) && ($past(count,1,reset)!=3'd0) &&
    count == ($past(count,1,reset)-3'd1)
  );

  cv_wrap_up:   cover property ( disable iff (reset)
    $past(up_down,1,reset) && ($past(count,1,reset)==3'd7) && (count==3'd0)
  );

  cv_wrap_down: cover property ( disable iff (reset)
    !$past(up_down,1,reset) && ($past(count,1,reset)==3'd0) && (count==3'd7)
  );

endmodule

// Bind into DUT instance(s) as needed:
// bind up_down_counter up_down_counter_sva sva (.*);