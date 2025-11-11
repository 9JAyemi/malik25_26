// SVA for commutation_top, timer, debouncer
// Quality-focused, concise, with key checks and coverage

// --------------- commutation_top SVA ---------------
module commutation_top_sva #(
  parameter STATE_IDLE    = 4'b0000,
  parameter STATE_ADVANCE = 4'b0001,
  parameter STATE_BREAK   = 4'b0010,
  parameter STATE_ALIGN   = 4'b0011
)(
  input  logic        clk,
  input  logic        reset_i,
  input  logic        enable_i,
  input  logic        advance_i,
  input  logic        break_i,
  input  logic        align_i,
  input  logic        direction_i,
  input  logic [3:0]  state_o
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset_i);

  // Synchronous reset drives IDLE (visible next cycle due to sampling in preponed region)
  assert property (@(posedge clk) reset_i |=> state_o == STATE_IDLE);

  // State always in defined set
  assert property (state_o inside {STATE_IDLE, STATE_ADVANCE, STATE_BREAK, STATE_ALIGN});

  // IDLE transitions (with priority: advance > break > align)
  assert property ((state_o==STATE_IDLE && !enable_i) |=> state_o==STATE_IDLE);
  assert property ((state_o==STATE_IDLE && enable_i && advance_i)                                   |=> state_o==STATE_ADVANCE);
  assert property ((state_o==STATE_IDLE && enable_i && !advance_i && break_i)                      |=> state_o==STATE_BREAK);
  assert property ((state_o==STATE_IDLE && enable_i && !advance_i && !break_i && align_i)          |=> state_o==STATE_ALIGN);
  assert property ((state_o==STATE_IDLE && enable_i && !advance_i && !break_i && !align_i)         |=> state_o==STATE_IDLE);

  // ADVANCE transitions
  assert property ((state_o==STATE_ADVANCE &&  direction_i) |=> state_o==STATE_IDLE);
  assert property ((state_o==STATE_ADVANCE && !direction_i) |=> state_o==STATE_ADVANCE);

  // BREAK/ALIGN are single-cycle, return to IDLE
  assert property ((state_o==STATE_BREAK) |=> state_o==STATE_IDLE);
  assert property ((state_o==STATE_ALIGN) |=> state_o==STATE_IDLE);

  // Coverage: all transition paths + priority case
  cover property (reset_i ##1 !reset_i ##1 state_o==STATE_IDLE);
  cover property (state_o==STATE_IDLE && enable_i && advance_i                                    ##1 state_o==STATE_ADVANCE);
  cover property (state_o==STATE_IDLE && enable_i && !advance_i && break_i                        ##1 state_o==STATE_BREAK);
  cover property (state_o==STATE_IDLE && enable_i && !advance_i && !break_i && align_i            ##1 state_o==STATE_ALIGN);
  cover property (state_o==STATE_ADVANCE && direction_i                                           ##1 state_o==STATE_IDLE);
  cover property (state_o==STATE_ADVANCE && !direction_i                                          ##1 state_o==STATE_ADVANCE);
  cover property (state_o==STATE_BREAK                                                            ##1 state_o==STATE_IDLE);
  cover property (state_o==STATE_ALIGN                                                            ##1 state_o==STATE_IDLE);
  cover property (state_o==STATE_IDLE && enable_i && advance_i && break_i && align_i              ##1 state_o==STATE_ADVANCE);
endmodule

bind commutation_top commutation_top_sva #(
  .STATE_IDLE(STATE_IDLE), .STATE_ADVANCE(STATE_ADVANCE), .STATE_BREAK(STATE_BREAK), .STATE_ALIGN(STATE_ALIGN)
) commutation_top_sva_i (
  .clk(clk), .reset_i(reset_i), .enable_i(enable_i), .advance_i(advance_i),
  .break_i(break_i), .align_i(align_i), .direction_i(direction_i), .state_o(state_o)
);

// --------------- timer SVA ---------------
module timer_sva (
  input  logic        clk,
  input  logic        reset_i,
  input  logic        enable_i,
  input  logic [15:0] compare_i,
  input  logic [15:0] autoreload_i,
  input  logic        compare_o,
  input  logic [15:0] value_o
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset_i);

  // Reset behavior
  assert property (@(posedge clk) reset_i |=> value_o == 16'h0);

  // compare_o equivalence
  assert property (compare_o <-> (value_o == compare_i));

  // Next-state semantics
  assert property (enable_i && (value_o == compare_i) |=> value_o == autoreload_i);
  assert property (enable_i && (value_o != compare_i) |=> value_o == $past(value_o) + 16'd1);

  // Hold when disabled
  assert property (!enable_i |=> value_o == $past(value_o));

  // Coverage
  cover property (enable_i && (value_o == compare_i) ##1 value_o == autoreload_i);
  cover property (enable_i && (value_o != compare_i) ##1 value_o == $past(value_o)+16'd1);
  cover property (!enable_i ##1 value_o == $past(value_o));
endmodule

bind timer timer_sva timer_sva_i (
  .clk(clk), .reset_i(reset_i), .enable_i(enable_i),
  .compare_i(compare_i), .autoreload_i(autoreload_i),
  .compare_o(compare_o), .value_o(value_o)
);

// --------------- debouncer SVA ---------------
module debouncer_sva #(
  parameter int DEBOUNCE_COUNT = 2
)(
  input  logic                          clk_i,
  input  logic                          reset_i,
  input  logic                          pin_i,
  input  logic                          pos_o,
  input  logic                          neg_o,
  input  logic                          debounced_o,
  input  logic [DEBOUNCE_COUNT-1:0]     counter,
  input  logic                          prev_pin_i
);
  default clocking cb @(posedge clk_i); endclocking
  default disable iff (reset_i);

  // Reset-visible next cycle values
  assert property (@(posedge clk_i) reset_i |=> counter=='0 && prev_pin_i==1'b0 && pos_o==1'b0 && neg_o==1'b0 && debounced_o==1'b0);

  // pos_o/neg_o = single-cycle pulses on pin edges, mutually exclusive
  assert property (pos_o |-> $rose(pin_i));
  assert property ($rose(pin_i) |-> pos_o);
  assert property (neg_o |-> $fell(pin_i));
  assert property ($fell(pin_i) |-> neg_o);
  assert property (pos_o |=> !pos_o);
  assert property (neg_o |=> !neg_o);
  assert property (!(pos_o && neg_o));

  // prev_pin_i tracks pin_i (1-cycle delayed)
  assert property (1'b1 |-> prev_pin_i == $past(pin_i));

  // Free-running counter increments every cycle (modulo width)
  assert property (1'b1 |=> counter == $past(counter) + {{(DEBOUNCE_COUNT-1){1'b0}},1'b1});

  // debounced_o matches equality condition to DEBOUNCE_COUNT
  assert property (debounced_o <-> (counter == DEBOUNCE_COUNT));

  // Coverage
  cover property ($rose(pin_i) ##0 pos_o);
  cover property ($fell(pin_i) ##0 neg_o);
  cover property (counter == DEBOUNCE_COUNT ##0 debounced_o);
endmodule

bind debouncer debouncer_sva #(.DEBOUNCE_COUNT(DEBOUNCE_COUNT)) debouncer_sva_i (
  .clk_i(clk_i), .reset_i(reset_i), .pin_i(pin_i),
  .pos_o(pos_o), .neg_o(neg_o), .debounced_o(debounced_o),
  .counter(counter), .prev_pin_i(prev_pin_i)
);