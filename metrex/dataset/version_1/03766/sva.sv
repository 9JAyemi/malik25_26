// SVA for CORDIC_FSM_v2
// Bind this checker to the DUT. Focused, high-quality safety + functional checks and coverage.
module CORDIC_FSM_v2_sva
(
  input  logic        clk, reset,
  input  logic        beg_FSM_CORDIC, ACK_FSM_CORDIC, operation, exception,
  input  logic [1:0]  shift_region_flag, cont_var,
  input  logic        ready_add_subt, max_tick_iter, min_tick_iter, max_tick_var, min_tick_var,
  input  logic        reset_reg_cordic, ready_CORDIC, beg_add_subt, ack_add_subt,
  input  logic        sel_mux_1, sel_mux_3,
  input  logic [1:0]  sel_mux_2,
  input  logic        enab_cont_iter, load_cont_iter, enab_cont_var,  load_cont_var,
  input  logic        enab_RB1, enab_RB2, enab_RB3,
  input  logic        enab_d_ff_Xn, enab_d_ff_Yn, enab_d_ff_Zn, enab_d_ff_out, enab_dff_5,
  input  logic        enab_reg_sel_mux1, enab_reg_sel_mux2, enab_reg_sel_mux3,
  input  logic [3:0]  state_reg
);

  // Mirror DUT state encodings
  localparam logic [3:0]
    est0  = 4'b0000, est1  = 4'b0001, est2  = 4'b0010, est3  = 4'b0011,
    est4  = 4'b0100, est5  = 4'b0101, est6  = 4'b0110, est7  = 4'b0111,
    est8  = 4'b1000, est9  = 4'b1001, est10 = 4'b1010, est11 = 4'b1011,
    est12 = 4'b1100, est13 = 4'b1101;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset behavior (async reset sampled on clk)
  assert property (@(posedge clk) reset |-> state_reg == est0);

  // State validity
  assert property (state_reg inside {est0,est1,est2,est3,est4,est5,est6,est7,est8,est9,est10,est11,est12,est13});

  // Next-state transitions
  assert property (state_reg==est0  |=> state_reg==est1);
  assert property ((state_reg==est1 &&  beg_FSM_CORDIC) |=> state_reg==est2);
  assert property ((state_reg==est1 && !beg_FSM_CORDIC) |=> state_reg==est1);
  assert property (state_reg==est2  |=> state_reg==est3);
  assert property (state_reg==est3  |=> state_reg==est4);
  assert property ((state_reg==est4 &&  exception) |=> state_reg==est0);
  assert property ((state_reg==est4 && !exception) |=> state_reg==est5);
  assert property (state_reg==est5  |=> state_reg==est6);
  assert property (state_reg==est6  |=> state_reg==est7);
  assert property (state_reg==est7  |=> state_reg==est8);
  assert property ((state_reg==est8 &&  ready_add_subt) |=> state_reg==est9);
  assert property ((state_reg==est8 && !ready_add_subt) |=> state_reg==est8);
  assert property ((state_reg==est9 &&  max_tick_iter)             |=> state_reg==est10);
  assert property ((state_reg==est9 && !max_tick_iter &&  max_tick_var) |=> state_reg==est3);
  assert property ((state_reg==est9 && !max_tick_iter && !max_tick_var) |=> state_reg==est6);
  assert property (state_reg==est10 |=> state_reg==est11);
  assert property (state_reg==est11 |=> state_reg==est12);
  assert property (state_reg==est12 |=> state_reg==est13);
  assert property ((state_reg==est13 &&  ACK_FSM_CORDIC) |=> state_reg==est0);
  assert property ((state_reg==est13 && !ACK_FSM_CORDIC) |=> state_reg==est13);

  // Output/state consistency (critical controls)
  assert property (ready_CORDIC      == (state_reg==est13));
  assert property (reset_reg_cordic  == (state_reg==est0));
  assert property (beg_add_subt      == (state_reg==est7));
  assert property (ack_add_subt      == (state_reg==est9));
  assert property (enab_RB1          == (state_reg==est2));
  assert property (enab_RB2          == (state_reg==est4));
  assert property (enab_RB3          == (state_reg==est5));
  assert property (enab_dff_5        == (state_reg==est11));
  assert property (enab_d_ff_out     == (state_reg==est12));
  assert property (enab_reg_sel_mux1 == (state_reg==est0 || state_reg==est3));
  assert property ((state_reg==est6) -> enab_reg_sel_mux2);
  assert property (enab_reg_sel_mux2 -> (state_reg==est6));
  assert property (enab_reg_sel_mux3 == (state_reg==est10));

  // Handshakes
  assert property (ack_add_subt |-> $past(state_reg==est8 && ready_add_subt));
  assert property (beg_add_subt |-> $past(state_reg==est6));
  assert property (ACK_FSM_CORDIC |-> ready_CORDIC);
  assert property ((ready_CORDIC && !ACK_FSM_CORDIC) |=> ready_CORDIC);

  // Counter enables/loads
  assert property ((state_reg==est2) -> (enab_cont_iter && load_cont_iter));
  assert property ((state_reg==est5) -> (enab_cont_var  && load_cont_var));
  assert property ((state_reg==est9 && !max_tick_iter &&  max_tick_var) -> enab_cont_iter);
  assert property ((state_reg==est9 && !max_tick_iter && !max_tick_var) -> enab_cont_var);

  // sel_mux_1 behavior (only in est3)
  assert property ((state_reg==est3)  -> (sel_mux_1 == ~min_tick_iter));
  assert property ((state_reg!=est3)  -> (sel_mux_1 == 1'b0));

  // sel_mux_2 function in est6
  let sel2_op0 = (shift_region_flag==2'b00) ? 2'b00 :
                 (shift_region_flag==2'b01) ? 2'b01 :
                 (shift_region_flag==2'b10) ? 2'b01 : 2'b00;
  let sel2_op1 = (shift_region_flag==2'b00) ? 2'b01 :
                 (shift_region_flag==2'b01) ? 2'b00 :
                 (shift_region_flag==2'b10) ? 2'b00 : 2'b01;
  let sel2_calc = max_tick_iter ? (operation ? sel2_op1 : sel2_op0) : cont_var;
  assert property ((state_reg==est6) -> (sel_mux_2 == sel2_calc));

  // sel_mux_3 function in est10
  let sel3_op0 = (shift_region_flag==2'b00) ? 1'b0 :
                 (shift_region_flag==2'b01) ? 1'b1 :
                 (shift_region_flag==2'b10) ? 1'b1 : 1'b0;
  let sel3_op1 = (shift_region_flag==2'b00) ? 1'b1 :
                 (shift_region_flag==2'b01) ? 1'b0 :
                 (shift_region_flag==2'b10) ? 1'b0 : 1'b1;
  let sel3_calc = operation ? sel3_op1 : sel3_op0;
  assert property ((state_reg==est10) -> (sel_mux_3 == sel3_calc));

  // enab_d_ff_* only in est8 when ready_add_subt, and exactly one
  assert property ((enab_d_ff_Xn || enab_d_ff_Yn || enab_d_ff_Zn) -> (state_reg==est8 && ready_add_subt));
  assert property ((state_reg==est8 && ready_add_subt) -> $onehot({enab_d_ff_Xn,enab_d_ff_Yn,enab_d_ff_Zn}));
  assert property ((state_reg!=est8 || !ready_add_subt) -> !(enab_d_ff_Xn || enab_d_ff_Yn || enab_d_ff_Zn));

  // Detailed enab_d_ff_* selection
  // max_tick_iter path: only Xn or Yn (no Zn)
  assert property ((state_reg==est8 && ready_add_subt &&  max_tick_iter && !operation && (shift_region_flag inside {2'b00,2'b11})) -> (enab_d_ff_Xn && !enab_d_ff_Yn && !enab_d_ff_Zn));
  assert property ((state_reg==est8 && ready_add_subt &&  max_tick_iter && !operation && (shift_region_flag inside {2'b01,2'b10})) -> (enab_d_ff_Yn && !enab_d_ff_Xn && !enab_d_ff_Zn));
  assert property ((state_reg==est8 && ready_add_subt &&  max_tick_iter &&  operation && (shift_region_flag inside {2'b00,2'b11})) -> (enab_d_ff_Yn && !enab_d_ff_Xn && !enab_d_ff_Zn));
  assert property ((state_reg==est8 && ready_add_subt &&  max_tick_iter &&  operation && (shift_region_flag inside {2'b01,2'b10})) -> (enab_d_ff_Xn && !enab_d_ff_Yn && !enab_d_ff_Zn));
  // !max_tick_iter path: Xn if min_tick_var, Zn if max_tick_var, else Yn
  assert property ((state_reg==est8 && ready_add_subt && !max_tick_iter &&  min_tick_var) -> (enab_d_ff_Xn && !enab_d_ff_Yn && !enab_d_ff_Zn));
  assert property ((state_reg==est8 && ready_add_subt && !max_tick_iter &&  max_tick_var) -> (enab_d_ff_Zn && !enab_d_ff_Xn && !enab_d_ff_Yn));
  assert property ((state_reg==est8 && ready_add_subt && !max_tick_iter && !min_tick_var && !max_tick_var) -> (enab_d_ff_Yn && !enab_d_ff_Xn && !enab_d_ff_Zn));

  // Mutual exclusivity (defensive)
  assert property ($onehot0({enab_d_ff_Xn,enab_d_ff_Yn,enab_d_ff_Zn}));

  // Coverage: state reachability and key branches
  cover property (state_reg==est0);
  cover property (state_reg==est1);
  cover property (state_reg==est2);
  cover property (state_reg==est3);
  cover property (state_reg==est4);
  cover property (state_reg==est5);
  cover property (state_reg==est6);
  cover property (state_reg==est7);
  cover property (state_reg==est8);
  cover property (state_reg==est9);
  cover property (state_reg==est10);
  cover property (state_reg==est11);
  cover property (state_reg==est12);
  cover property (state_reg==est13);

  cover property (state_reg==est4 && exception);
  cover property (state_reg==est4 && !exception);
  cover property (state_reg==est6 && !max_tick_iter);
  cover property (state_reg==est6 &&  max_tick_iter);
  cover property (state_reg==est8 && ready_add_subt);
  cover property (state_reg==est9 &&  max_tick_iter);
  cover property (state_reg==est9 && !max_tick_iter &&  max_tick_var);
  cover property (state_reg==est9 && !max_tick_iter && !max_tick_var);
  cover property (state_reg==est10 && operation==1'b0 && shift_region_flag==2'b01);
  cover property (state_reg==est10 && operation==1'b1 && shift_region_flag==2'b00);
  cover property (state_reg==est13 && ACK_FSM_CORDIC);

endmodule

// Bind to DUT
bind CORDIC_FSM_v2 CORDIC_FSM_v2_sva i_CORDIC_FSM_v2_sva (
  .clk(clk),
  .reset(reset),
  .beg_FSM_CORDIC(beg_FSM_CORDIC),
  .ACK_FSM_CORDIC(ACK_FSM_CORDIC),
  .operation(operation),
  .exception(exception),
  .shift_region_flag(shift_region_flag),
  .cont_var(cont_var),
  .ready_add_subt(ready_add_subt),
  .max_tick_iter(max_tick_iter),
  .min_tick_iter(min_tick_iter),
  .max_tick_var(max_tick_var),
  .min_tick_var(min_tick_var),
  .reset_reg_cordic(reset_reg_cordic),
  .ready_CORDIC(ready_CORDIC),
  .beg_add_subt(beg_add_subt),
  .ack_add_subt(ack_add_subt),
  .sel_mux_1(sel_mux_1),
  .sel_mux_3(sel_mux_3),
  .sel_mux_2(sel_mux_2),
  .enab_cont_iter(enab_cont_iter),
  .load_cont_iter(load_cont_iter),
  .enab_cont_var(enab_cont_var),
  .load_cont_var(load_cont_var),
  .enab_RB1(enab_RB1),
  .enab_RB2(enab_RB2),
  .enab_RB3(enab_RB3),
  .enab_d_ff_Xn(enab_d_ff_Xn),
  .enab_d_ff_Yn(enab_d_ff_Yn),
  .enab_d_ff_Zn(enab_d_ff_Zn),
  .enab_d_ff_out(enab_d_ff_out),
  .enab_dff_5(enab_dff_5),
  .enab_reg_sel_mux1(enab_reg_sel_mux1),
  .enab_reg_sel_mux2(enab_reg_sel_mux2),
  .enab_reg_sel_mux3(enab_reg_sel_mux3),
  .state_reg(state_reg)
);