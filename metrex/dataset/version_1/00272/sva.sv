// SVA checker for RGB1_RGB2
module RGB1_RGB2_sva (
  input  logic        clk,
  input  logic        Btn_R,
  input  logic        Btn_L,
  input  logic [2:0]  RGB1,
  input  logic [2:0]  RGB2,
  input  logic [1:0]  state,
  input  logic [1:0]  nextState
);
  default clocking cb @(posedge clk); endclocking

  // past-valid guard
  logic past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Basic sanity
  a_no_x_inputs:        assert property (!$isunknown({Btn_R,Btn_L}));
  a_state_range:        assert property (state inside {[2'd0:2'd2]} && nextState inside {[2'd0:2'd2]});
  a_state_follows_next: assert property (past_valid |-> state == $past(nextState));

  // Outputs well-formed and identical
  a_outputs_onehot_eq:  assert property ($onehot(RGB1) && RGB1 === RGB2 && !$isunknown({RGB1,RGB2}));

  // Outputs reflect previous cycle's state (Moore, one-cycle latency)
  a_out_match_pstate:   assert property (past_valid |-> (RGB1 == (3'b001 << $past(state))) && (RGB2 == (3'b001 << $past(state))));

  // Transition behavior: Right only (increment mod 3)
  a_r_0_to_1: assert property ((state==2'd0 &&  Btn_R && !Btn_L) |=> state==2'd1));
  a_r_1_to_2: assert property ((state==2'd1 &&  Btn_R && !Btn_L) |=> state==2'd2));
  a_r_2_to_0: assert property ((state==2'd2 &&  Btn_R && !Btn_L) |=> state==2'd0));

  // Transition behavior: Left only (decrement mod 3)
  a_l_0_to_2: assert property ((state==2'd0 && !Btn_R &&  Btn_L) |=> state==2'd2));
  a_l_1_to_0: assert property ((state==2'd1 && !Btn_R &&  Btn_L) |=> state==2'd0));
  a_l_2_to_1: assert property ((state==2'd2 && !Btn_R &&  Btn_L) |=> state==2'd1));

  // Both pressed: Left has priority
  a_lr_0_to_2: assert property ((state==2'd0 && Btn_R && Btn_L) |=> state==2'd2));
  a_lr_1_to_0: assert property ((state==2'd1 && Btn_R && Btn_L) |=> state==2'd0));
  a_lr_2_to_1: assert property ((state==2'd2 && Btn_R && Btn_L) |=> state==2'd1));

  // Idle hold when settled (no new request)
  a_idle_hold_ns_eq_s: assert property (past_valid && !Btn_R && !Btn_L && state==$past(state) |-> nextState==state);

  // Coverage
  c_visit_all_states:    cover property (state==2'd0 ##1 state==2'd1 ##1 state==2'd2);
  c_right_ring:          cover property ((state==2'd0 && Btn_R && !Btn_L) ##1 (state==2'd1 && Btn_R && !Btn_L) ##1 (state==2'd2 && Btn_R && !Btn_L) ##1 state==2'd0);
  c_left_ring:           cover property ((state==2'd0 && Btn_L && !Btn_R) ##1 (state==2'd2 && Btn_L && !Btn_R) ##1 (state==2'd1 && Btn_L && !Btn_R) ##1 state==2'd0);
  c_both_priority_each:  cover property ((state==2'd0 && Btn_R && Btn_L) ##1 state==2'd2);
  c_both_priority_each2: cover property ((state==2'd1 && Btn_R && Btn_L) ##1 state==2'd0);
  c_both_priority_each3: cover property ((state==2'd2 && Btn_R && Btn_L) ##1 state==2'd1);
  c_output_sequence:     cover property (RGB1==3'b001 ##1 RGB1==3'b010 ##1 RGB1==3'b100 ##1 RGB1==3'b001);
endmodule

// Bind into DUT (accesses internal state/nextState)
bind RGB1_RGB2 RGB1_RGB2_sva i_rgb_sva (
  .clk      (clk),
  .Btn_R    (Btn_R),
  .Btn_L    (Btn_L),
  .RGB1     (RGB1),
  .RGB2     (RGB2),
  .state    (state),
  .nextState(nextState)
);