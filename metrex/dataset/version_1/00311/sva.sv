// SVA for sequential_logic_block
// Bindable, concise, and checks full FSM next-state/output behavior with essential coverage.

module sequential_logic_block_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [2:0]  x,
  input  logic        f,
  input  logic [2:0]  state
);

  // State encodings (match DUT)
  localparam logic [2:0] S0=3'b000, S1=3'b001, S2=3'b010, S3=3'b011,
                         S4=3'b100, S5=3'b101, S6=3'b110, S7=3'b111;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // No X in key regs when not in reset
  assert property (!$isunknown({state,f})));

  // Asynchronous reset effect (same-cycle after NBA) and synchronous while asserted
  assert property (@(posedge reset) ##0 (state==S0 && f==1'b0));
  assert property (@(posedge clk) reset |-> (state==S0 && f==1'b0));

  // State0 holds and forces f=0
  property p_s0_hold; (state==S0) |=> (state==S0 && f==1'b0); endproperty
  assert property (p_s0_hold);
  cover  property (p_s0_hold);

  // S1 transitions
  property p_s1_t; (state==S1 && x==3'b001) |=> (state==S2 && f==1'b1); endproperty
  property p_s1_e; (state==S1 && x!=3'b001) |=> (state==S0 && f==1'b0); endproperty
  assert property (p_s1_t);  assert property (p_s1_e);
  cover  property (p_s1_t);

  // S2 transitions
  property p_s2_t; (state==S2 && x==3'b010) |=> (state==S3 && f==1'b1); endproperty
  property p_s2_e; (state==S2 && x!=3'b010) |=> (state==S0 && f==1'b0); endproperty
  assert property (p_s2_t);  assert property (p_s2_e);
  cover  property (p_s2_t);

  // S3 transitions
  property p_s3_t; (state==S3 && x==3'b011) |=> (state==S4 && f==1'b1); endproperty
  property p_s3_e; (state==S3 && x!=3'b011) |=> (state==S0 && f==1'b0); endproperty
  assert property (p_s3_t);  assert property (p_s3_e);
  cover  property (p_s3_t);

  // S4 transition
  property p_s4; (state==S4) |=> (state==S0 && f==1'b0); endproperty
  assert property (p_s4);
  cover  property (p_s4);

  // S5 transitions
  property p_s5_t; (state==S5 && x==3'b001) |=> (state==S6 && f==1'b1); endproperty
  property p_s5_e; (state==S5 && x!=3'b001) |=> (state==S0 && f==1'b0); endproperty
  assert property (p_s5_t);  assert property (p_s5_e);
  cover  property (p_s5_t);

  // S6 transitions
  property p_s6_t; (state==S6 && x==3'b010) |=> (state==S7 && f==1'b1); endproperty
  property p_s6_e; (state==S6 && x!=3'b010) |=> (state==S0 && f==1'b0); endproperty
  assert property (p_s6_t);  assert property (p_s6_e);
  cover  property (p_s6_t);

  // S7 transitions
  property p_s7_t; (state==S7 && x==3'b011) |=> (state==S0 && f==1'b1); endproperty
  property p_s7_e; (state==S7 && x!=3'b011) |=> (state==S0 && f==1'b0); endproperty
  assert property (p_s7_t);  assert property (p_s7_e);
  cover  property (p_s7_t);

  // State space coverage (reveals unreachable states)
  cover property (state==S0);
  cover property (state==S1);
  cover property (state==S2);
  cover property (state==S3);
  cover property (state==S4);
  cover property (state==S5);
  cover property (state==S6);
  cover property (state==S7);

endmodule

// Bind into DUT (state is internal)
bind sequential_logic_block sequential_logic_block_sva sva (
  .clk  (clk),
  .reset(reset),
  .x    (x),
  .f    (f),
  .state(state)
);