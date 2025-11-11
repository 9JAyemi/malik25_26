// SVA for fsm_example
// Bind into the DUT to access internals without changing RTL.
module fsm_example_sva;
  // Expect to be bound into fsm_example; the following are in scope:
  // clk, rst_n, next_state, state_out, current_state, next_state_reg, S0..S3

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  function automatic [1:0] inc_wrap(input [1:0] s);
    case (s)
      S0: inc_wrap = S1;
      S1: inc_wrap = S2;
      S2: inc_wrap = S3;
      S3: inc_wrap = S0;
      default: inc_wrap = S0;
    endcase
  endfunction

  // No X/unknowns when out of reset
  a_no_x:       assert property (!$isunknown({current_state, state_out, next_state, next_state_reg}));

  // Reset values (checked at clock edges while reset is asserted)
  a_reset_vals: assert property (@(posedge clk) !rst_n |-> (current_state==S0 && state_out==S0));

  // Combinational next-state function correctness
  a_comb_next:  assert property (next_state_reg == (next_state ? inc_wrap(current_state) : current_state));

  // Sequential state update on clock
  a_hold:       assert property (!next_state |=> current_state == $past(current_state));
  a_advance:    assert property ( next_state |=> current_state == inc_wrap($past(current_state)));

  // Output follows current_state by exactly 1 cycle
  a_out_lag1:   assert property ($past(rst_n) |-> state_out == $past(current_state));

  // Coverage
  c_visit_all:  cover property (current_state==S0 ##1 current_state==S1 ##1 current_state==S2 ##1 current_state==S3);
  c_wrap:       cover property (current_state==S3 && next_state ##1 current_state==S0);
  c_hold:       cover property (current_state==S2 && !next_state ##1 current_state==S2);
endmodule

bind fsm_example fsm_example_sva fsm_example_sva_i();