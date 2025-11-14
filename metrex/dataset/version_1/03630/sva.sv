// SVA for FSM. Concise, high-quality checks and coverage.
// Bind into DUT to access internals.
module fsm_sva #(parameter int n=4, m=2, s=8)
(
  input  logic                 clk,
  input  logic [n-1:0]         in,
  input  logic [m-1:0]         out,
  input  logic [s-1:0]         state,
  input  logic [s-1:0]         next_state,
  input  logic [m-1:0]         output_reg
);

  // Default sampling clock
  default clocking cb @(posedge clk); endclocking

  // Combinational function checks (equivalent to transition/output tables)
  // Ensure state encoding uses only 3 LSBs and zero-extends.
  assert property (!$isunknown(in) |-> (next_state[2:0] == in[2:0] && next_state[s-1:3] == '0));
  assert property (!$isunknown(in) |-> (output_reg == in[1:0]));

  // Sequential pipeline checks (registered propagation)
  assert property (!$isunknown($past(next_state)) |-> state == $past(next_state));
  assert property (!$isunknown($past(output_reg)) |-> out   == $past(output_reg));

  // No X/Z propagation when inputs are known
  assert property (!$isunknown(in)        |-> (!$isunknown(next_state) && !$isunknown(output_reg)));
  assert property (!$isunknown($past(in)) |-> (!$isunknown(state)      && !$isunknown(out)));

  // Coverage: exercise all input codes and observe correct registered state/output one cycle later
  genvar i;
  generate
    for (i = 0; i < (1<<n); i++) begin : C_PIPE
      localparam logic [n-1:0] IN_VAL  = i;
      localparam logic [2:0]   S_VAL   = i[2:0];
      localparam logic [m-1:0] OUT_VAL = i[m-1:0];
      cover property (in == IN_VAL ##1 (state[2:0] == S_VAL && out == OUT_VAL));
    end
  endgenerate

endmodule

// Bind SVA to the DUT (names must match DUT internals)
bind FSM fsm_sva #(.n(n), .m(m), .s(s)) u_fsm_sva (.*);