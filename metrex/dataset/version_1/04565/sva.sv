// SystemVerilog Assertions for Gato_FSM
// Bindable SVA module + bind statement

module Gato_FSM_sva (
  input logic        clk,
  input logic        reset,
  input logic        p1_mm, p2_mm,
  input logic        p1_tie, p1_loss, p1_win,
  input logic        p2_tie, p2_loss, p2_win,
  input logic        turno_p1, turno_p2,
  input logic        verifica_status,
  input logic        win_game, loss_game, tie_game,
  input logic [3:0]  state
);
  // Mirror DUT encodings
  localparam int P1_Move   = 0;
  localparam int P1_Status = 1;
  localparam int P2_Move   = 2;
  localparam int P2_Status = 3;
  localparam int Win       = 4;
  localparam int Tie       = 5;
  localparam int Loss      = 6;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic sanity and legality
  a_state_known:    assert property (!$isunknown(state));
  a_state_legal:    assert property (state inside {P1_Move,P1_Status,P2_Move,P2_Status,Win,Tie,Loss});
  a_turn_onehot:    assert property (turno_p1 ^ turno_p2);
  a_vstatus_match:  assert property (verifica_status == ((state==P1_Status)||(state==P2_Status)));
  a_out_known:      assert property (!$isunknown({turno_p1,turno_p2,verifica_status,win_game,loss_game,tie_game}));

  // Reset behavior (sampled on clk while reset asserted)
  a_reset_state: assert property (@(posedge clk) reset |-> state==P1_Move);

  // Output mapping per state
  a_p1_move_outs:   assert property (state==P1_Move   |-> !verifica_status &&  turno_p1 && !turno_p2);
  a_p1_stat_outs:   assert property (state==P1_Status |->  verifica_status && !turno_p1 &&  turno_p2);
  a_p2_move_outs:   assert property (state==P2_Move   |-> !verifica_status && !turno_p1 &&  turno_p2);
  a_p2_stat_outs:   assert property (state==P2_Status |->  verifica_status &&  turno_p1 && !turno_p2);

  // Terminal states sticky and mutually-exclusive outputs
  a_win_sticky:     assert property (state==Win  |=> state==Win);
  a_tie_sticky:     assert property (state==Tie  |=> state==Tie);
  a_loss_sticky:    assert property (state==Loss |=> state==Loss);

  a_win_out:        assert property (state==Win  |->  win_game && !loss_game && !tie_game);
  a_tie_out:        assert property (state==Tie  |->  tie_game && !win_game  && !loss_game);
  a_loss_out:       assert property (state==Loss |->  loss_game&& !win_game  && !tie_game);

  a_nonterm_outs0:  assert property (state inside {P1_Move,P1_Status,P2_Move,P2_Status}
                                     |-> !win_game && !loss_game && !tie_game);

  // Input one-hot0 sanity when status is being checked
  a_p1_status_inputs_onehot0: assert property (state==P1_Status |-> $onehot0({p1_tie,p1_loss,p1_win}));
  a_p2_status_inputs_onehot0: assert property (state==P2_Status |-> $onehot0({p2_tie,p2_loss,p2_win}));

  // Next-state transition checks
  // P1 move stage
  a_p1move_stay:       assert property (state==P1_Move   && (p1_mm==0) |=> state==P1_Move);
  a_p1move_to_stat:    assert property (state==P1_Move   && (p1_mm==1) |=> state==P1_Status);

  // P1 status decisions
  a_p1stat_to_tie:     assert property (state==P1_Status &&  p1_tie && !p1_loss && !p1_win |=> state==Tie);
  a_p1stat_to_loss:    assert property (state==P1_Status &&  p1_win && !p1_tie  && !p1_loss |=> state==Loss);
  a_p1stat_to_p2move:  assert property (state==P1_Status && !p1_tie && !p1_win && (p2_mm==0) |=> state==P2_Move);

  // P2 move stage
  a_p2move_stay:       assert property (state==P2_Move   && (p2_mm==0) |=> state==P2_Move);
  a_p2move_to_stat:    assert property (state==P2_Move   && (p2_mm==1) |=> state==P2_Status);

  // P2 status decisions
  a_p2stat_to_tie:     assert property (state==P2_Status &&  p2_tie && !p2_loss && !p2_win |=> state==Tie);
  a_p2stat_to_win:     assert property (state==P2_Status &&  p2_win && !p2_tie && !p2_loss |=> state==Win);
  a_p2stat_to_p1move:  assert property (state==P2_Status && !p2_tie && !p2_win && (p1_mm==0) |=> state==P1_Move);

  // Coverage: reachability and key transitions
  c_start:             cover property (state==P1_Move);
  c_all_states:        cover property (state inside {P1_Move,P1_Status,P2_Move,P2_Status,Win,Tie,Loss});
  c_p1_path:           cover property (state==P1_Move && p1_mm ##1 state==P1_Status && !p1_tie && !p1_win && (p2_mm==0) ##1 state==P2_Move);
  c_p2_path:           cover property (state==P2_Move && p2_mm ##1 state==P2_Status && !p2_tie && !p2_win && (p1_mm==0) ##1 state==P1_Move);
  c_tie_from_p1:       cover property (state==P1_Status && p1_tie && !p1_win && !p1_loss ##1 state==Tie && tie_game);
  c_win_from_p2:       cover property (state==P2_Status && p2_win && !p2_tie && !p2_loss ##1 state==Win && win_game);
  c_loss_from_p1:      cover property (state==P1_Status && p1_win && !p1_tie && !p1_loss ##1 state==Loss && loss_game);
endmodule

bind Gato_FSM Gato_FSM_sva
  i_Gato_FSM_sva (
    .clk(clk),
    .reset(reset),
    .p1_mm(p1_mm),
    .p2_mm(p2_mm),
    .p1_tie(p1_tie),
    .p1_loss(p1_loss),
    .p1_win(p1_win),
    .p2_tie(p2_tie),
    .p2_loss(p2_loss),
    .p2_win(p2_win),
    .turno_p1(turno_p1),
    .turno_p2(turno_p2),
    .verifica_status(verifica_status),
    .win_game(win_game),
    .loss_game(loss_game),
    .tie_game(tie_game),
    .state(state)
  );