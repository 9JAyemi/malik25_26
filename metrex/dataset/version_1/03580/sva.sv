// SVA for edge_detect_mux
// Bind this file to the DUT: bind edge_detect_mux edge_detect_mux_sva sva_i (.*);

module edge_detect_mux_sva (
  input logic clk, rst_n,
  input logic a, b, c, select,
  input logic rise, fall, w, x, y, z,
  input logic [1:0] state
);

  // Mirror DUT encodings
  localparam logic [1:0] IDLE=2'b00, RISING_EDGE=2'b01, FALLING_EDGE=2'b10, MUX_SELECT=2'b11;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Reset behavior and legal state space
  assert property (!rst_n |-> state == IDLE);
  assert property (!$isunknown(state));
  assert property (state inside {IDLE, RISING_EDGE, FALLING_EDGE, MUX_SELECT});

  // Deterministic state progression
  assert property (state == IDLE         |=> state == RISING_EDGE);
  assert property (state == RISING_EDGE  |=> state == FALLING_EDGE);
  assert property (state == FALLING_EDGE |=> state == MUX_SELECT);
  assert property (state == MUX_SELECT   |=> state == IDLE);

  // Output correctness per state
  assert property (state == IDLE         |-> rise == 1'b0 && fall == 1'b0);
  assert property (state == RISING_EDGE  |-> rise === a   && fall == 1'b0);
  assert property (state == FALLING_EDGE |-> rise == 1'b0 && fall === ~a);
  assert property (state == MUX_SELECT   |-> rise == 1'b0 && fall == 1'b0);

  // Mutual exclusion
  assert property (!(rise && fall));

  // MUX outputs and mapping (4-state accurate)
  assert property (w === select);
  assert property ((select === 1'b0) |-> x === a);
  assert property ((select === 1'b1) |-> x === b);
  assert property ((select !== 1'b0 && select !== 1'b1) |-> x === 1'b0); // default branch behavior
  assert property (y == 1'b0 && z == 1'b0);

  // No X-propagation on outputs when driving inputs are known
  assert property ((!$isunknown({a,b,select})) |-> !$isunknown({rise,fall,w,x}));

  // Coverage
  sequence s_full_loop;
    state==IDLE ##1 state==RISING_EDGE ##1 state==FALLING_EDGE ##1 state==MUX_SELECT ##1 state==IDLE;
  endsequence
  cover property (s_full_loop);

  cover property (state==RISING_EDGE  && a==1 && rise==1 && fall==0);
  cover property (state==FALLING_EDGE && a==0 && fall==1 && rise==0);

  cover property (select===1'b0 && x===a && y==0 && z==0);
  cover property (select===1'b1 && x===b && y==0 && z==0);

endmodule

bind edge_detect_mux edge_detect_mux_sva sva_i (.*);