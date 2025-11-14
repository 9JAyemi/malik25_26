// SVA for d_flip_flop
module d_flip_flop_sva (input logic D, CLK, Q);

  // Functional: Q captures D on the same rising edge (after NBA updates)
  a_q_follows_d: assert property (@(posedge CLK) ##0 (Q === D));

  // Sanity: Q must not update on falling edge of CLK
  a_no_update_on_negedge: assert property (@(negedge CLK) $stable(Q));

  // Knownness: if D is known at the edge, Q must be known right after
  a_no_x_when_d_known: assert property (@(posedge CLK) !$isunknown(D) |-> ##0 !$isunknown(Q));

  // Coverage: observe Q rise/fall and hold behavior
  c_q_rise: cover property (@(posedge CLK) ##0 $rose(Q));
  c_q_fall: cover property (@(posedge CLK) ##0 $fell(Q));
  c_q_hold: cover property (@(posedge CLK) ($stable(D)) ##0 ($stable(Q)));

  // Coverage: both logic values seen on Q
  c_q0: cover property (@(posedge CLK) ##0 (Q === 1'b0));
  c_q1: cover property (@(posedge CLK) ##0 (Q === 1'b1));

endmodule

bind d_flip_flop d_flip_flop_sva sva_dff (.*);