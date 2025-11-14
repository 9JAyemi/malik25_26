// SVA for rx_data_receive
module rx_data_receive_sva (
  input logic               posedge_clk,
  input logic               rx_resetn,

  input logic               ready_control_p_r,
  input logic               ready_data_p_r,
  input logic               ready_control,
  input logic               ready_data,

  input logic               parity_rec_c,
  input logic               parity_rec_d,
  input logic               parity_rec_c_gen,
  input logic               parity_rec_d_gen,

  input logic [2:0]         control_p_r,
  input logic [2:0]         control_l_r,
  input logic [8:0]         dta_timec_p,

  input logic [1:0]         state_data_process,
  input logic [1:0]         next_state_data_process,

  input logic               last_is_control,
  input logic               last_is_data,
  input logic               last_is_timec,

  input logic               rx_error_c,
  input logic               rx_error_d,
  input logic               rx_got_fct,

  input logic [8:0]         rx_data_flag,
  input logic [7:0]         timecode
);

default clocking cb @ (posedge posedge_clk); endclocking
default disable iff (!rx_resetn);

// Reset values
assert property (@cb !rx_resetn |-> (state_data_process==2'd0 &&
                                     !last_is_control && !last_is_data && !last_is_timec &&
                                     rx_data_flag==9'd0 && timecode==8'd0 &&
                                     !rx_error_c && !rx_error_d && !rx_got_fct));

// State register follows next_state
assert property (@cb state_data_process == $past(next_state_data_process));

// next_state combinational correctness
assert property (@cb next_state_data_process ==
                 (state_data_process==2'd0 ? ((ready_control_p_r||ready_data_p_r)?2'd1:2'd0) :
                  (state_data_process==2'd1 ? ((ready_control||ready_data)?2'd0:2'd1) : 2'd0)));

// State encoding domain
assert property (@cb state_data_process inside {2'd0,2'd1});

// One-hot(0) last flags
assert property (@cb $onehot0({last_is_control,last_is_data,last_is_timec}));

// FSM transition behavior
assert property (@cb (state_data_process==2'd0 && (ready_control_p_r||ready_data_p_r)) |-> ##1 state_data_process==2'd1);
assert property (@cb (state_data_process==2'd1 && (ready_control||ready_data))         |-> ##1 state_data_process==2'd0);
assert property (@cb (state_data_process==2'd0 && !(ready_control_p_r||ready_data_p_r))|-> ##1 state_data_process==2'd0);
assert property (@cb (state_data_process==2'd1 && !(ready_control||ready_data))        |-> ##1 state_data_process==2'd1);

// Hold in state 1
assert property (@cb (state_data_process==2'd1) |-> ($stable(rx_data_flag) && $stable(timecode)));

// State 0, idle branch holds and clears got_fct
assert property (@cb (state_data_process==2'd0 && !ready_control_p_r && !ready_data_p_r)
                 |=> (!rx_got_fct && rx_data_flag==$past(rx_data_flag) && timecode==$past(timecode)));

// Control preview effects (state 0)
assert property (@cb (state_data_process==2'd0 && ready_control_p_r)
                 |=> ( last_is_control && !last_is_data && !last_is_timec));

assert property (@cb (state_data_process==2'd0 && ready_control_p_r && (control_l_r!=3'd7) && (control_p_r==3'd4)) |=> rx_got_fct);
assert property (@cb (state_data_process==2'd0 && ready_control_p_r && !((control_l_r!=3'd7) && (control_p_r==3'd4))) |=> !rx_got_fct);

// Control-set flags into rx_data_flag
assert property (@cb (state_data_process==2'd0 && ready_control_p_r && control_p_r==3'd6) |=> rx_data_flag==9'b100000001);
assert property (@cb (state_data_process==2'd0 && ready_control_p_r && control_p_r==3'd5) |=> rx_data_flag==9'b100000000);
assert property (@cb (state_data_process==2'd0 && ready_control_p_r && !(control_p_r inside {3'd5,3'd6})) |=> rx_data_flag==$past(rx_data_flag));

// Data/timecode preview effects (state 0)
assert property (@cb (state_data_process==2'd0 && ready_data_p_r && control_p_r==3'd7)
                 |=> (timecode==dta_timec_p[7:0] && !last_is_control && !last_is_data && last_is_timec && !rx_got_fct));

assert property (@cb (state_data_process==2'd0 && ready_data_p_r && control_p_r!=3'd7)
                 |=> (rx_data_flag==dta_timec_p && !last_is_control && last_is_data && !last_is_timec && !rx_got_fct));

// Parity check, state 1 (control)
assert property (@cb (state_data_process==2'd1 && ready_control_p_r && (parity_rec_c_gen != parity_rec_c)) |=> rx_error_c);
assert property (@cb (state_data_process==2'd1 && ready_control_p_r && (parity_rec_c_gen == parity_rec_c)) |=> rx_error_c==$past(rx_error_c));

// Parity check, state 1 (data)
assert property (@cb (state_data_process==2'd1 && ready_data_p_r && (parity_rec_d_gen != parity_rec_d)) |=> rx_error_d);
assert property (@cb (state_data_process==2'd1 && ready_data_p_r && (parity_rec_d_gen == parity_rec_d)) |=> rx_error_d==$past(rx_error_d));

// Parity error stickiness
assert property (@cb rx_error_c |-> $stable(rx_error_c));
assert property (@cb rx_error_d |-> $stable(rx_error_d));

// rx_got_fct behavior in state 1
assert property (@cb (state_data_process==2'd1 && ready_control_p_r) |=> rx_got_fct==$past(rx_got_fct));
assert property (@cb (state_data_process==2'd1 && ready_data_p_r)    |=> !rx_got_fct);
assert property (@cb (state_data_process==2'd1 && !ready_control_p_r && !ready_data_p_r) |=> !rx_got_fct);

// Functional coverage
cover property (@cb (state_data_process==2'd0 && (ready_control_p_r||ready_data_p_r)) ##1
                     state_data_process==2'd1 ##[1:10] (ready_control||ready_data) ##1
                     state_data_process==2'd0);

cover property (@cb (state_data_process==2'd0 && ready_control_p_r && (control_l_r!=3'd7) && (control_p_r==3'd4)));
cover property (@cb (state_data_process==2'd0 && ready_control_p_r && control_p_r==3'd6));
cover property (@cb (state_data_process==2'd0 && ready_control_p_r && control_p_r==3'd5));
cover property (@cb (state_data_process==2'd0 && ready_data_p_r && control_p_r==3'd7));
cover property (@cb (state_data_process==2'd0 && ready_data_p_r && control_p_r!=3'd7));
cover property (@cb (state_data_process==2'd1 && ready_control_p_r && (parity_rec_c_gen != parity_rec_c)));
cover property (@cb (state_data_process==2'd1 && ready_data_p_r   && (parity_rec_d_gen != parity_rec_d)));

endmodule

bind rx_data_receive rx_data_receive_sva sva_i (
  .posedge_clk(posedge_clk),
  .rx_resetn(rx_resetn),
  .ready_control_p_r(ready_control_p_r),
  .ready_data_p_r(ready_data_p_r),
  .ready_control(ready_control),
  .ready_data(ready_data),
  .parity_rec_c(parity_rec_c),
  .parity_rec_d(parity_rec_d),
  .parity_rec_c_gen(parity_rec_c_gen),
  .parity_rec_d_gen(parity_rec_d_gen),
  .control_p_r(control_p_r),
  .control_l_r(control_l_r),
  .dta_timec_p(dta_timec_p),
  .state_data_process(state_data_process),
  .next_state_data_process(next_state_data_process),
  .last_is_control(last_is_control),
  .last_is_data(last_is_data),
  .last_is_timec(last_is_timec),
  .rx_error_c(rx_error_c),
  .rx_error_d(rx_error_d),
  .rx_got_fct(rx_got_fct),
  .rx_data_flag(rx_data_flag),
  .timecode(timecode)
);