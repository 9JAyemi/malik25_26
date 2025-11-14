// SVA for GrayCodeStateMachine
module GrayCodeStateMachine_sva #(parameter int n=3, m=(1<<n)) (
  input logic              clk,
  input logic              rst,
  input logic              en,
  input logic [n-1:0]      out,
  input logic [n-1:0]      state,
  input logic [n-1:0]      next_state
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset behavior
  assert property (rst |-> (state=='0 && out=='0));

  // No X/Z after reset
  assert property (!$isunknown({state,out,next_state}));

  // Hold when disabled
  assert property (!en |-> (state==$past(state) && out==$past(out)));

  // Sequential update uses next_state (D flop connectivity)
  assert property (en |-> state==$past(next_state));

  // out lags state by exactly one cycle when enabled
  assert property (en |-> out==$past(state));

  // Combinational next_state must be Gray-adjacent to state
  assert property ($onehot(state ^ next_state));

  // Sequential Gray transition when enabled
  assert property (en |-> $onehot(state ^ $past(state)));

  // Full-cycle length m when enabled continuously starting from 0
  property p_full_cycle;
    (state=='0 && en) ##1 (en [* (m-1)]) |-> state=='0;
  endproperty
  assert property (p_full_cycle);

  // Coverage
  genvar i;
  generate
    for (i=0; i<m; i++) begin : C_STATES
      cover property (state==i);
    end
  endgenerate
  cover property (en ##1 $onehot(state ^ $past(state)));
  cover property ((state=='0 && en) ##1 (en [* (m-1)]) ##1 state=='0);
endmodule

bind GrayCodeStateMachine
  GrayCodeStateMachine_sva #(.n(n), .m(m)) gc_sva (
    .clk(clk),
    .rst(rst),
    .en(en),
    .out(out),
    .state(state),
    .next_state(next_state)
  );