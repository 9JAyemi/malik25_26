// SVA for no_input_circuit
module no_input_circuit_sva #(
  parameter logic [1:0] S0 = 2'b00,
  parameter logic [1:0] S1 = 2'b01,
  parameter logic [1:0] S2 = 2'b10
)(
  input logic        clk,
  input logic        reset,
  input logic [1:0]  state,
  input logic        out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // No X/Z on key regs when not in reset
  assert property (!$isunknown({state,out}));

  // Legal state encodings only
  assert property (state inside {S0,S1,S2});

  // Output matches state
  assert property (state==S0 |-> out==0);
  assert property (state==S1 |-> out==1);
  assert property (state==S2 |-> out==0);

  // State transitions and next-cycle outputs
  assert property (state==S0 |=> (state==S1 && out==1));
  assert property (state==S1 |=> (state==S2 && out==1));
  assert property (state==S2 |=> (state==S2 && out==0));

  // Eventually reach S2 within 2 cycles after reset deassert
  assert property (@(posedge clk) $fell(reset) |-> ##[0:2] (state==S2));

  // Once in S2, stay there with out==0 until reset
  assert property (state==S2 |-> (state==S2 && out==0)[*]);

  // Synchronous reset behavior (checked even while reset=1)
  assert property (@(posedge clk) reset |=> (state==S0 && out==0));

  // Functional coverage
  cover property (@(posedge clk) $fell(reset) ##1 state==S0 ##1 state==S1 ##1 state==S2);
  cover property (@(posedge clk) $fell(reset) ##1 out==0 ##1 out==1 ##1 out==1 ##1 out==0);
  cover property (state==S2 [*3]);
endmodule

bind no_input_circuit no_input_circuit_sva #(.S0(S0), .S1(S1), .S2(S2)) i_no_input_circuit_sva (
  .clk  (clk),
  .reset(reset),
  .state(state),
  .out  (out)
);