// SVA for fsm_3input_1output
// Bind this module to the DUT. Focused, concise, full functional checks + key coverage.

module fsm_3input_1output_sva (
  input logic        clk,
  input logic        reset,
  input logic        a,b,c,
  input logic [1:0]  state,
  input logic [1:0]  next_state,
  input logic        d
);
  // Mirror DUT encodings locally
  localparam logic [1:0] S0 = 2'b00, S1 = 2'b01;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Shorthands
  let s0 = (state == S0);
  let s1 = (state == S1);
  let c_s0_tos1 =  a & ~b & ~c;
  let c_s0_keep0 = ~a & ~b &  c;
  let c_s1_tos0 = ~a & ~b & ~c;
  let c_s1_keep1 = ~a & ~b &  c;

  // Asynchronous reset puts state to S0 immediately
  assert property (@(posedge reset) ##0 state == S0);

  // State must be legal when not in reset
  assert property (state inside {S0,S1});

  // Combinational next_state/d truth table (sampled on clk)
  assert property (s0 && c_s0_tos1            |-> next_state == S1 && d == 1'b0);
  assert property (s0 && c_s0_keep0           |-> next_state == S0 && d == 1'b0);
  assert property (s0 && !(c_s0_tos1||c_s0_keep0) |-> next_state == S0 && d == 1'b1);

  assert property (s1 && c_s1_tos0            |-> next_state == S0 && d == 1'b1);
  assert property (s1 && c_s1_keep1           |-> next_state == S1 && d == 1'b1);
  assert property (s1 && !(c_s1_tos0||c_s1_keep1) |-> next_state == S1 && d == 1'b0);

  // Default recovery behavior if illegal state ever appears
  assert property ((!(s0||s1)) |-> next_state == S0 && d == 1'b0);

  // Registered update: state follows next_state on next clock
  assert property (@(posedge clk) disable iff (reset || $initstate)
                   state == $past(next_state));

  // No X/Z on key regs (outside reset)
  assert property (!$isunknown({state,next_state,d}));

  // Coverage: hit each branch and transition
  cover property (s0 && c_s0_tos1 ##1 state == S1);
  cover property (s0 && c_s0_keep0  ##1 state == S0);
  cover property (s0 && !(c_s0_tos1||c_s0_keep0) ##1 state == S0);

  cover property (s1 && c_s1_tos0 ##1 state == S0);
  cover property (s1 && c_s1_keep1 ##1 state == S1);
  cover property (s1 && !(c_s1_tos0||c_s1_keep1) ##1 state == S1);

  cover property (d == 1'b0);
  cover property (d == 1'b1);
endmodule

// Bind to DUT
bind fsm_3input_1output fsm_3input_1output_sva u_fsm_3input_1output_sva(
  .clk(clk), .reset(reset), .a(a), .b(b), .c(c),
  .state(state), .next_state(next_state), .d(d)
);