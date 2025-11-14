// SVA checker for Altera_UP_PS2_Data_In
// Bind example:
// bind Altera_UP_PS2_Data_In Altera_UP_PS2_Data_In_sva sva (.*);

module Altera_UP_PS2_Data_In_sva
(
  input  logic        clk,
  input  logic        reset,

  input  logic        wait_for_incoming_data,
  input  logic        start_receiving_data,

  input  logic        ps2_clk_posedge,
  input  logic        ps2_clk_negedge,
  input  logic        ps2_data,

  input  logic [7:0]  received_data,
  input  logic        received_data_en,

  input  logic [3:0]  data_count,
  input  logic [7:0]  data_shift_reg,

  input  logic [2:0]  s_ps2_receiver,
  input  logic [2:0]  ns_ps2_receiver
);

  localparam PS2_STATE_0_IDLE          = 3'h0;
  localparam PS2_STATE_1_WAIT_FOR_DATA = 3'h1;
  localparam PS2_STATE_2_DATA_IN       = 3'h2;
  localparam PS2_STATE_3_PARITY_IN     = 3'h3;
  localparam PS2_STATE_4_STOP_IN       = 3'h4;

  default clocking cb @(posedge clk); endclocking
  // Most assertions disabled during reset; add explicit reset checks where needed
  default disable iff (reset);

  // Reset behavior
  a_reset_state: assert property (@cb reset |-> s_ps2_receiver == PS2_STATE_0_IDLE);

  // State machine sanity
  a_state_legal: assert property (@cb s_ps2_receiver inside {
                                    PS2_STATE_0_IDLE, PS2_STATE_1_WAIT_FOR_DATA,
                                    PS2_STATE_2_DATA_IN, PS2_STATE_3_PARITY_IN,
                                    PS2_STATE_4_STOP_IN });

  a_state_follows_ns: assert property (@cb s_ps2_receiver == $past(ns_ps2_receiver));

  // IDLE transitions (priority to wait_for_incoming_data)
  a_idle_to_wait: assert property (@cb
    s_ps2_receiver == PS2_STATE_0_IDLE &&
    wait_for_incoming_data && !received_data_en |=> s_ps2_receiver == PS2_STATE_1_WAIT_FOR_DATA);

  a_idle_to_data: assert property (@cb
    s_ps2_receiver == PS2_STATE_0_IDLE &&
    !wait_for_incoming_data && start_receiving_data && !received_data_en
    |=> s_ps2_receiver == PS2_STATE_2_DATA_IN);

  a_idle_stay: assert property (@cb
    s_ps2_receiver == PS2_STATE_0_IDLE &&
    !wait_for_incoming_data && !start_receiving_data
    |=> s_ps2_receiver == PS2_STATE_0_IDLE);

  // WAIT_FOR_DATA transitions
  a_wait_to_data: assert property (@cb
    s_ps2_receiver == PS2_STATE_1_WAIT_FOR_DATA &&
    ps2_clk_posedge && (ps2_data==1'b0)
    |=> s_ps2_receiver == PS2_STATE_2_DATA_IN);

  a_wait_abort: assert property (@cb
    s_ps2_receiver == PS2_STATE_1_WAIT_FOR_DATA && !wait_for_incoming_data
    |=> s_ps2_receiver == PS2_STATE_0_IDLE);

  // DATA_IN transition
  a_data_to_parity: assert property (@cb
    s_ps2_receiver == PS2_STATE_2_DATA_IN &&
    ps2_clk_posedge && (data_count == 3'h7)
    |=> s_ps2_receiver == PS2_STATE_3_PARITY_IN);

  // PARITY -> STOP, STOP -> IDLE
  a_parity_to_stop: assert property (@cb
    s_ps2_receiver == PS2_STATE_3_PARITY_IN && ps2_clk_posedge
    |=> s_ps2_receiver == PS2_STATE_4_STOP_IN);

  a_stop_to_idle: assert property (@cb
    s_ps2_receiver == PS2_STATE_4_STOP_IN && ps2_clk_posedge
    |=> s_ps2_receiver == PS2_STATE_0_IDLE);

  // data_count behavior
  a_cnt_inc: assert property (@cb
    s_ps2_receiver == PS2_STATE_2_DATA_IN && ps2_clk_posedge
    |-> data_count == $past(data_count) + 1);

  a_cnt_hold: assert property (@cb
    s_ps2_receiver == PS2_STATE_2_DATA_IN && !ps2_clk_posedge
    |-> $stable(data_count));

  a_cnt_zero_outside_data: assert property (@cb
    s_ps2_receiver != PS2_STATE_2_DATA_IN |-> data_count == 0);

  a_cnt_range: assert property (@cb data_count <= 4'd8);

  // Shifter behavior
  a_shift_only_on_cap: assert property (@cb
    $changed(data_shift_reg) |-> $past(s_ps2_receiver == PS2_STATE_2_DATA_IN && ps2_clk_posedge));

  a_shift_relation: assert property (@cb
    s_ps2_receiver == PS2_STATE_2_DATA_IN && ps2_clk_posedge
    |-> data_shift_reg == { $past(ps2_data), $past(data_shift_reg[7:1]) });

  // received_data behavior
  a_rd_only_in_stop: assert property (@cb
    $changed(received_data) |-> $past(s_ps2_receiver == PS2_STATE_4_STOP_IN));

  a_rd_eq_shift_in_stop: assert property (@cb
    s_ps2_receiver == PS2_STATE_4_STOP_IN |-> received_data == data_shift_reg);

  // received_data_en pulse correctness
  a_rden_only_in_stop_edge: assert property (@cb
    received_data_en |-> (s_ps2_receiver == PS2_STATE_4_STOP_IN && ps2_clk_posedge));

  a_rden_assert_when_stop_edge: assert property (@cb
    s_ps2_receiver == PS2_STATE_4_STOP_IN && ps2_clk_posedge |-> received_data_en);

  a_rden_one_cycle_pulse: assert property (@cb
    $rose(received_data_en) |=> !received_data_en);

  // Full-frame coverage from WAIT path (start bit + 8 data + parity + stop)
  c_full_frame_wait: cover property (@cb
    s_ps2_receiver == PS2_STATE_0_IDLE ##1
    (wait_for_incoming_data && !received_data_en) ##1
    s_ps2_receiver == PS2_STATE_1_WAIT_FOR_DATA ##1
    (ps2_clk_posedge && ps2_data==1'b0) ##1
    s_ps2_receiver == PS2_STATE_2_DATA_IN ##
    ((ps2_clk_posedge && s_ps2_receiver == PS2_STATE_2_DATA_IN)[*8]) ##1
    s_ps2_receiver == PS2_STATE_3_PARITY_IN ##1
    ps2_clk_posedge ##1
    s_ps2_receiver == PS2_STATE_4_STOP_IN ##1
    (ps2_clk_posedge && received_data_en) ##1
    s_ps2_receiver == PS2_STATE_0_IDLE);

  // Full-frame coverage from immediate start_receiving_data path
  c_full_frame_start: cover property (@cb
    s_ps2_receiver == PS2_STATE_0_IDLE ##1
    (!wait_for_incoming_data && start_receiving_data && !received_data_en) ##1
    s_ps2_receiver == PS2_STATE_2_DATA_IN ##
    ((ps2_clk_posedge && s_ps2_receiver == PS2_STATE_2_DATA_IN)[*8]) ##1
    s_ps2_receiver == PS2_STATE_3_PARITY_IN ##1
    ps2_clk_posedge ##1
    s_ps2_receiver == PS2_STATE_4_STOP_IN ##1
    (ps2_clk_posedge && received_data_en) ##1
    s_ps2_receiver == PS2_STATE_0_IDLE);

  // Coverage: WAIT aborted back to IDLE
  c_wait_abort: cover property (@cb
    s_ps2_receiver == PS2_STATE_1_WAIT_FOR_DATA ##1
    !wait_for_incoming_data ##1
    s_ps2_receiver == PS2_STATE_0_IDLE);

  // Coverage: Priority check when both requests asserted in IDLE
  c_priority_wait_over_start: cover property (@cb
    s_ps2_receiver == PS2_STATE_0_IDLE ##1
    (wait_for_incoming_data && start_receiving_data && !received_data_en) ##1
    s_ps2_receiver == PS2_STATE_1_WAIT_FOR_DATA);

endmodule