// SVA for state_machine
// Bind into the DUT to access internal signals
module state_machine_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        x,
  input  logic [5:0]  state,
  input  logic [5:0]  Y,
  input  logic        Y2,
  input  logic        Y4
);
  localparam logic [5:0] A = 6'b000001;

  function automatic logic [5:0] rot1 (input logic [5:0] s);
    rot1 = {s[4:0], s[5]};
  endfunction
  function automatic logic [5:0] rot2 (input logic [5:0] s);
    rot2 = {s[3:0], s[5:4]};
  endfunction

  default clocking cb @(posedge clk); endclocking

  // Reset puts state to A in the same cycle
  assert property (cb reset |-> ##0 (state == A));

  // State/Y one-hot and mapping
  assert property (cb disable iff (reset) $onehot(state));
  assert property (cb ##0 (Y == state));
  assert property (cb $onehot(Y));
  assert property (cb Y2 == state[2]);
  assert property (cb Y4 == state[4]);

  // Next-state function: x=1 -> +1 step, x=0 -> +2 steps (mod 6)
  assert property (cb disable iff (reset)
                   state == ( $past(x) ? rot1($past(state)) : rot2($past(state)) ));

  // No self-loops when not in reset
  assert property (cb disable iff (reset) state != $past(state));

  // Basic X-check (optional but useful)
  assert property (cb !$isunknown({state,Y,Y2,Y4}));

  // Coverage
  cover property (cb state == A);
  cover property (cb disable iff (reset) x[*6] ##1 (state == $past(state,6)));   // all-1 path wraps in 6
  cover property (cb disable iff (reset) (!x)[*3] ##1 (state == $past(state,3))); // all-0 path wraps in 3
  cover property (cb Y2);  // visit state C
  cover property (cb Y4);  // visit state E
endmodule

bind state_machine state_machine_sva
  u_state_machine_sva (
    .clk  (clk),
    .reset(reset),
    .x    (x),
    .state(state),
    .Y    (Y),
    .Y2   (Y2),
    .Y4   (Y4)
  );