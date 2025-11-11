// SVA for flow_ctrl_tx
// Bind module (non-intrusive) that checks key behavior and provides concise coverage

module flow_ctrl_tx_sva
  #(parameter SHIFT = 6,
    parameter W = 16+SHIFT)
(
  input              rst,
  input              tx_clk,
  input              tx_pause_en,
  input       [15:0] pause_quanta,
  input              pause_quanta_val,
  input              paused,
  input              pause_apply,

  // Internal DUT state (bound hierarchically)
  input       [W-1:0] pause_quanta_counter,
  input               pqval_d1,
  input               pqval_d2
);

  default clocking cb @(posedge tx_clk); endclocking
  default disable iff (rst);

  // Reset behavior (async reset observed synchronously)
  assert property (@(posedge tx_clk) rst |-> pause_quanta_counter == '0);
  assert property (@(posedge tx_clk) $rose(rst) |=> pause_quanta_counter == '0);

  // Internal 2FF edge-detector correctness
  assert property (pqval_d1 == $past(pause_quanta_val));
  assert property (pqval_d2 == $past(pqval_d1));

  // Load on pause_quanta_val rising edge (one-cycle later per design)
  assert property ($rose(pause_quanta_val) |=> pause_quanta_counter == {pause_quanta, {SHIFT{1'b0}}});

  // Assume/check pause_quanta is stable across the handshake capture window
  assert property ($rose(pause_quanta_val) |-> $stable(pause_quanta)[*2]);

  // Decrement only when counting and paused, unless a load is pending (load has priority)
  assert property ((pause_quanta_counter != '0) && paused && !$rose(pause_quanta_val)
                   |=> pause_quanta_counter == $past(pause_quanta_counter) - 1);

  // Hold when not paused (and no load)
  assert property ((pause_quanta_counter != '0) && !paused && !$rose(pause_quanta_val)
                   |=> pause_quanta_counter == $past(pause_quanta_counter));

  // No underflow: when zero (and no load), stays zero
  assert property ((pause_quanta_counter == '0) && !$rose(pause_quanta_val)
                   |=> pause_quanta_counter == '0);

  // Monotonic non-increasing when no load
  assert property (!$rose(pause_quanta_val) |-> pause_quanta_counter <= $past(pause_quanta_counter));

  // pause_apply is a pure function of tx_pause_en and counter!=0
  assert property (pause_apply == (tx_pause_en && (pause_quanta_counter != '0)));

  // Coverage

  // Cover: nonzero load then pause_apply asserts with tx_pause_en
  cover property ($rose(pause_quanta_val) && (pause_quanta != 16'd0)
                  ##1 (tx_pause_en && pause_apply));

  // Cover: reload while counting (load priority over decrement)
  cover property ((pause_quanta_counter != '0)
                  ##1 $rose(pause_quanta_val)
                  ##1 pause_quanta_counter == {pause_quanta, {SHIFT{1'b0}}});

  // Cover: counter nonzero but pause_apply blocked by tx_pause_en=0
  cover property ($rose(pause_quanta_val) && (pause_quanta != 16'd0)
                  ##1 (!tx_pause_en && !pause_apply));

endmodule


// Bind into DUT (connects to internal regs/wires by name inside flow_ctrl_tx)
bind flow_ctrl_tx flow_ctrl_tx_sva
  #(.SHIFT(6), .W(22))
  i_flow_ctrl_tx_sva (
    .rst(rst),
    .tx_clk(tx_clk),
    .tx_pause_en(tx_pause_en),
    .pause_quanta(pause_quanta),
    .pause_quanta_val(pause_quanta_val),
    .paused(paused),
    .pause_apply(pause_apply),
    .pause_quanta_counter(pause_quanta_counter),
    .pqval_d1(pqval_d1),
    .pqval_d2(pqval_d2)
  );