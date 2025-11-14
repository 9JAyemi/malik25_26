// SVA for FSM_Bola
// Bind these assertions to the DUT

module FSM_Bola_sva
(
  input  logic        clock,
  input  logic        reset,
  input  logic        start_ball,
  input  logic        busy_ball,
  input  logic        actualizar_bola,
  input  logic        revisar_bordes_bola,
  input  logic [2:0]  state
);
  // Local copies of state encodings
  localparam int STATE_0 = 0;
  localparam int STATE_1 = 1;
  localparam int STATE_2 = 2;
  localparam int STATE_3 = 3;

  // Basic X-checks (outside reset)
  assert property (@(posedge clock) reset || !$isunknown({state,busy_ball,actualizar_bola,revisar_bordes_bola}));

  // Reset behavior
  assert property (@(posedge clock) reset |-> (state==STATE_0 && !actualizar_bola && !revisar_bordes_bola && !busy_ball));

  // State legality (post-reset)
  assert property (@(posedge clock) disable iff (reset) state inside {STATE_0,STATE_1,STATE_2,STATE_3});

  // Busy equivalence
  assert property (@(posedge clock) disable iff (reset) (busy_ball == (state!=STATE_0)));

  // Next-state function
  assert property (@(posedge clock) disable iff (reset) (state==STATE_0 && !start_ball) |=> state==STATE_0);
  assert property (@(posedge clock) disable iff (reset) (state==STATE_0 &&  start_ball) |=> state==STATE_1);
  assert property (@(posedge clock) disable iff (reset) (state==STATE_1) |=> state==STATE_2);
  assert property (@(posedge clock) disable iff (reset) (state==STATE_2) |=> state==STATE_3);
  assert property (@(posedge clock) disable iff (reset) (state==STATE_3) |=> state==STATE_0);

  // Output correctness per state (single-cycle pulses)
  assert property (@(posedge clock) disable iff (reset) (state==STATE_1) |-> ( actualizar_bola && !revisar_bordes_bola));
  assert property (@(posedge clock) disable iff (reset) (state==STATE_2) |-> (!actualizar_bola &&  revisar_bordes_bola));
  assert property (@(posedge clock) disable iff (reset) (state inside {STATE_0,STATE_3}) |-> (!actualizar_bola && !revisar_bordes_bola));

  // Pulse width sanity: outputs only asserted in their state
  assert property (@(posedge clock) disable iff (reset) actualizar_bola      |-> state==STATE_1);
  assert property (@(posedge clock) disable iff (reset) revisar_bordes_bola |-> state==STATE_2);

  // Progress: any busy episode returns to idle in 3 cycles
  assert property (@(posedge clock) disable iff (reset) (state!=STATE_0) |-> ##3 state==STATE_0);

  // Full transaction check and cover
  property p_full_txn;
    @(posedge clock) disable iff (reset)
      (state==STATE_0 && start_ball)
      |=> (state==STATE_1 &&  actualizar_bola && !revisar_bordes_bola &&  busy_ball)
       ##1 (state==STATE_2 && !actualizar_bola &&  revisar_bordes_bola &&  busy_ball)
       ##1 (state==STATE_3 && !actualizar_bola && !revisar_bordes_bola &&  busy_ball)
       ##1 (state==STATE_0 && !busy_ball);
  endproperty
  assert property (p_full_txn);
  cover  property (p_full_txn);

  // Busy high exactly for 3 cycles per start
  assert property (@(posedge clock) disable iff (reset)
                   (state==STATE_0 && start_ball) |=> busy_ball[*3] ##1 !busy_ball);

  // Simple state coverage
  cover property (@(posedge clock) disable iff (reset) state==STATE_1);
  cover property (@(posedge clock) disable iff (reset) state==STATE_2);
  cover property (@(posedge clock) disable iff (reset) state==STATE_3);
endmodule

bind FSM_Bola FSM_Bola_sva sva_inst(
  .clock(clock),
  .reset(reset),
  .start_ball(start_ball),
  .busy_ball(busy_ball),
  .actualizar_bola(actualizar_bola),
  .revisar_bordes_bola(revisar_bordes_bola),
  .state(state)
);