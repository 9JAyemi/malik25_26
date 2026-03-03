// SVA for debouncer. Bind this file to the DUT.
// Focus: counter correctness, m_tick, FSM legality/transitions, db behavior, and key coverage.

module debouncer_sva #(parameter int N=19)
(
  input logic               clk, reset, sw, db,
  input logic [N-1:0]       q_reg,
  input logic [2:0]         state_reg,
  input logic               m_tick
);

  // Mirror DUT state encodings
  localparam logic [2:0]
    zero    = 3'b000,
    wait1_1 = 3'b001,
    wait1_2 = 3'b010,
    wait1_3 = 3'b011,
    one     = 3'b100,
    wait0_1 = 3'b101,
    wait0_2 = 3'b110,
    wait0_3 = 3'b111;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic X checks (at clock)
  a_known_io:     assert property (!$isunknown({sw, db, m_tick, state_reg}));

  // Asynchronous reset drives state_reg to zero
  a_async_rst:    assert property (@(posedge reset) state_reg==zero);
  a_sync_rst:     assert property (@(posedge clk) reset |-> state_reg==zero);

  // Counter increments by 1 every clock; m_tick reflects q_reg==0
  a_cnt_step:     assert property (!$isunknown($past(q_reg)) |-> q_reg == $past(q_reg)+1);
  a_tick_def:     assert property (!$isunknown(q_reg) |-> m_tick == (q_reg==0));

  // State must always be legal
  a_state_legal:  assert property (state_reg inside {zero,wait1_1,wait1_2,wait1_3,one,wait0_1,wait0_2,wait0_3});

  // db is 1 only in one/wait0_* states
  a_db_map:       assert property (db == (state_reg inside {one,wait0_1,wait0_2,wait0_3}));

  // FSM transitions: rising path
  a_z_hold:       assert property (state_reg==zero   && !sw        |=> state_reg==zero);
  a_z_to_w11:     assert property (state_reg==zero   &&  sw        |=> state_reg==wait1_1);

  a_w11_drop:     assert property (state_reg==wait1_1 && !sw       |=> state_reg==zero);
  a_w11_tick:     assert property (state_reg==wait1_1 &&  sw && m_tick |=> state_reg==wait1_2);
  a_w11_wait:     assert property (state_reg==wait1_1 &&  sw && !m_tick |=> state_reg==wait1_1);

  a_w12_drop:     assert property (state_reg==wait1_2 && !sw       |=> state_reg==zero);
  a_w12_tick:     assert property (state_reg==wait1_2 &&  sw && m_tick |=> state_reg==wait1_3);
  a_w12_wait:     assert property (state_reg==wait1_2 &&  sw && !m_tick |=> state_reg==wait1_2);

  a_w13_drop:     assert property (state_reg==wait1_3 && !sw       |=> state_reg==zero);
  a_w13_tick:     assert property (state_reg==wait1_3 &&  sw && m_tick |=> state_reg==one);
  a_w13_wait:     assert property (state_reg==wait1_3 &&  sw && !m_tick |=> state_reg==wait1_3);

  // FSM transitions: falling path
  a_one_hold:     assert property (state_reg==one     &&  sw       |=> state_reg==one);
  a_one_to_w01:   assert property (state_reg==one     && !sw       |=> state_reg==wait0_1);

  a_w01_raise:    assert property (state_reg==wait0_1 &&  sw       |=> state_reg==one);
  a_w01_tick:     assert property (state_reg==wait0_1 && !sw && m_tick |=> state_reg==wait0_2);
  a_w01_wait:     assert property (state_reg==wait0_1 && !sw && !m_tick |=> state_reg==wait0_1);

  a_w02_raise:    assert property (state_reg==wait0_2 &&  sw       |=> state_reg==one);
  a_w02_tick:     assert property (state_reg==wait0_2 && !sw && m_tick |=> state_reg==wait0_3);
  a_w02_wait:     assert property (state_reg==wait0_2 && !sw && !m_tick |=> state_reg==wait0_2);

  a_w03_raise:    assert property (state_reg==wait0_3 &&  sw       |=> state_reg==one);
  a_w03_tick:     assert property (state_reg==wait0_3 && !sw && m_tick |=> state_reg==zero);
  a_w03_wait:     assert property (state_reg==wait0_3 && !sw && !m_tick |=> state_reg==wait0_3);

  // db edges only at debounced boundaries, caused by prior tick
  a_db_rise_only: assert property ($rose(db) |-> $past(state_reg)==wait1_3 && state_reg==one && $past(m_tick));
  a_db_fall_only: assert property ($fell(db) |-> $past(state_reg)==wait0_3 && state_reg==zero && $past(m_tick));

  // Coverage
  c_tick:         cover property (m_tick);

  c_all_states:   cover property (state_reg inside {zero,wait1_1,wait1_2,wait1_3,one,wait0_1,wait0_2,wait0_3});

  // Debounced press: stay high through 3 ticks to reach 'one'
  c_press:        cover property (
                     state_reg==zero ##[1:$]
                     (sw && state_reg==wait1_1) ##[1:$]
                     (sw && state_reg==wait1_2) ##[1:$]
                     (sw && state_reg==wait1_3) ##1
                     (sw && m_tick) ##1 state_reg==one
                   );

  // Debounced release: stay low through 3 ticks to reach 'zero'
  c_release:      cover property (
                     state_reg==one ##[1:$]
                     (!sw && state_reg==wait0_1) ##[1:$]
                     (!sw && state_reg==wait0_2) ##[1:$]
                     (!sw && state_reg==wait0_3) ##1
                     (!sw && m_tick) ##1 state_reg==zero
                   );

  // Bounce aborts
  c_bounce_up_abort:   cover property (state_reg==wait1_2 ##1 !sw ##1 state_reg==zero);
  c_bounce_down_abort: cover property (state_reg==wait0_2 ##1  sw ##1 state_reg==one);

  // db edges covered
  c_db_rise:      cover property ($rose(db));
  c_db_fall:      cover property ($fell(db));

endmodule

// Bind into DUT
bind debouncer debouncer_sva #(.N(N)) debouncer_sva_i
(
  .clk(clk),
  .reset(reset),
  .sw(sw),
  .db(db),
  .q_reg(q_reg),
  .state_reg(state_reg),
  .m_tick(m_tick)
);