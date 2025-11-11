// SVA checker for FSM. Binds into the DUT and uses an event-based clock on any input change.
// Focuses on state legality, next-state transitions, output mapping, and basic coverage.

module fsm_sva #(parameter int n=4, m=2)
(
  input  logic [n-1:0] in,
  input  logic [m-1:0] out,
  input  logic [1:0]   state
);
  // State encodings (must match DUT)
  localparam logic [1:0] S0_0 = 2'b00;
  localparam logic [1:0] S0_1 = 2'b01;
  localparam logic [1:0] S1_0 = 2'b10;
  localparam logic [1:0] S1_1 = 2'b11;

  // Static parameter sanity
  initial begin
    if (n < 4) $error("FSM SVA: parameter n must be >= 4 (uses in[3:0])");
    if (m != 2) $error("FSM SVA: parameter m must be == 2 (out is 2 bits)");
  end

  // Event-based sampling: toggle on any input vector change
  logic mon_clk = 0;
  always @(in) mon_clk = ~mon_clk;

  default clocking cb @(posedge mon_clk or negedge mon_clk); endclocking

  `define DDISABLE disable iff ($isunknown({in,state,out}))

  // State legality and out known
  a_legal_state: assert property (`DDISABLE state inside {S0_0,S0_1,S1_0,S1_1});
  a_out_known  : assert property (`DDISABLE !$isunknown(out));

  // Next-state behavior: transition on condition, else hold
  a_ns_s00_set: assert property (`DDISABLE (state==S0_0 && in[2]) |-> ##0 state==S0_1);
  a_ns_s00_hld: assert property (`DDISABLE (state==S0_0 && !in[2]) |-> ##0 state==S0_0);

  a_ns_s01_set: assert property (`DDISABLE (state==S0_1 && in[1]) |-> ##0 state==S1_0);
  a_ns_s01_hld: assert property (`DDISABLE (state==S0_1 && !in[1]) |-> ##0 state==S0_1);

  a_ns_s10_set: assert property (`DDISABLE (state==S1_0 && in[2]) |-> ##0 state==S1_1);
  a_ns_s10_hld: assert property (`DDISABLE (state==S1_0 && !in[2]) |-> ##0 state==S1_0);

  a_ns_s11_set: assert property (`DDISABLE (state==S1_1 && in[0]) |-> ##0 state==S0_0);
  a_ns_s11_hld: assert property (`DDISABLE (state==S1_1 && !in[0]) |-> ##0 state==S1_1);

  // No illegal jumps: only hold or the defined next-state
  a_only_ns_s00: assert property (`DDISABLE (state==S0_0) |-> ##0 (state inside {S0_0,S0_1}));
  a_only_ns_s01: assert property (`DDISABLE (state==S0_1) |-> ##0 (state inside {S0_1,S1_0}));
  a_only_ns_s10: assert property (`DDISABLE (state==S1_0) |-> ##0 (state inside {S1_0,S1_1}));
  a_only_ns_s11: assert property (`DDISABLE (state==S1_1) |-> ##0 (state inside {S1_1,S0_0}));

  // Output mapping per state (same-event, after DUT updates)
  a_out_s00: assert property (`DDISABLE (state==S0_0) |-> ##0 (out == {in[0], in[1]}));
  a_out_s01: assert property (`DDISABLE (state==S0_1) |-> ##0 (out == {in[3], in[2]}));
  a_out_s10: assert property (`DDISABLE (state==S1_0) |-> ##0 (out == {in[0], in[3]}));
  a_out_s11: assert property (`DDISABLE (state==S1_1) |-> ##0 (out == {in[1], in[2]}));

  // Coverage: visit states and exercise each transition
  c_state_cov   : cover property (state inside {S0_0,S0_1,S1_0,S1_1});
  c_s00_to_s01  : cover property ((state==S0_0 && in[2]) |-> ##0 state==S0_1);
  c_s01_to_s10  : cover property ((state==S0_1 && in[1]) |-> ##0 state==S1_0);
  c_s10_to_s11  : cover property ((state==S1_0 && in[2]) |-> ##0 state==S1_1);
  c_s11_to_s00  : cover property ((state==S1_1 && in[0]) |-> ##0 state==S0_0);

  `undef DDISABLE
endmodule

// Bind into all FSM instances; ports include internal 'state'
bind FSM fsm_sva #(.n(n), .m(m)) fsm_sva_i (.in(in), .out(out), .state(state));