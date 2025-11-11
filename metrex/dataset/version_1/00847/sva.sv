// SVA for adder_subtractor_4bit + embedded full_adder_1bit instances
// Focus: functional correctness, carry-chain connectivity, and key internal invariants.

module adder_subtractor_4bit_sva (
  input logic        CLK,
  input logic        RST,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic        SEL,
  input logic [3:0]  Y,
  input logic        COUT,
  input logic [3:0]  sum,
  input logic [3:0]  neg_b,
  input logic [3:0]  twos_comp_b,

  // full_adder_1bit ports for each bit-slice
  input logic        fa0_A,    fa0_B,    fa0_CIN,    fa0_SUM,    fa0_COUT,
  input logic        fa1_A,    fa1_B,    fa1_CIN,    fa1_SUM,    fa1_COUT,
  input logic        fa2_A,    fa2_B,    fa2_CIN,    fa2_SUM,    fa2_COUT,
  input logic        fa3_A,    fa3_B,    fa3_CIN,    fa3_SUM,    fa3_COUT
);

  function automatic [4:0] addsub_ref(input logic [3:0] a,
                                      input logic [3:0] b,
                                      input logic       sel);
    addsub_ref = {1'b0,a} + {1'b0,(sel ? b : ~b)} + sel;
  endfunction

  default clocking cb @(posedge CLK); endclocking
  default disable iff (RST);

  // No-X on inputs and outputs
  property p_inputs_known; !$isunknown({A,B,SEL}); endproperty
  assert property (p_inputs_known);
  assert property (p_inputs_known |-> !$isunknown({Y,COUT}));

  // Golden functional check: {COUT,Y} must equal A + (SEL ? B : ~B) + SEL
  assert property (p_inputs_known |-> {COUT,Y} == addsub_ref(A,B,SEL));

  // Internal invariant: two's complement of B
  assert property (p_inputs_known |-> neg_b == (~B + 4'd1));

  // full_adder_1bit truth table checks (all four slices)
  assert property (p_inputs_known |-> fa0_SUM == (fa0_A ^ fa0_B ^ fa0_CIN));
  assert property (p_inputs_known |-> fa0_COUT == ((fa0_A & fa0_B) | (fa0_B & fa0_CIN) | (fa0_A & fa0_CIN)));
  assert property (p_inputs_known |-> fa1_SUM == (fa1_A ^ fa1_B ^ fa1_CIN));
  assert property (p_inputs_known |-> fa1_COUT == ((fa1_A & fa1_B) | (fa1_B & fa1_CIN) | (fa1_A & fa1_CIN)));
  assert property (p_inputs_known |-> fa2_SUM == (fa2_A ^ fa2_B ^ fa2_CIN));
  assert property (p_inputs_known |-> fa2_COUT == ((fa2_A & fa2_B) | (fa2_B & fa2_CIN) | (fa2_A & fa2_CIN)));
  assert property (p_inputs_known |-> fa3_SUM == (fa3_A ^ fa3_B ^ fa3_CIN));
  assert property (p_inputs_known |-> fa3_COUT == ((fa3_A & fa3_B) | (fa3_B & fa3_CIN) | (fa3_A & fa3_CIN)));

  // Carry-chain connectivity must be ripple COUT->CIN
  assert property (p_inputs_known |-> fa1_CIN == fa0_COUT);
  assert property (p_inputs_known |-> fa2_CIN == fa1_COUT);
  assert property (p_inputs_known |-> fa3_CIN == fa2_COUT);
  assert property (p_inputs_known |-> COUT     == fa3_COUT);

  // Coverage: add overflow, sub borrow, zero results, SEL toggles
  cover property (p_inputs_known && SEL  && addsub_ref(A,B,SEL)[4]);        // add overflow
  cover property (p_inputs_known && !SEL && !addsub_ref(A,B,SEL)[4]);       // sub borrow
  cover property (p_inputs_known &&  SEL && addsub_ref(A,B,SEL)[3:0]==0);   // add wraps to zero
  cover property (p_inputs_known && !SEL && addsub_ref(A,B,SEL)[3:0]==0);   // A==B -> zero
  cover property (p_inputs_known && $rose(SEL));
  cover property (p_inputs_known && $fell(SEL));

endmodule

// Bind into the DUT; hierarchical connects expose internals and FA ports
bind adder_subtractor_4bit adder_subtractor_4bit_sva u_sva (
  .CLK(CLK), .RST(RST),
  .A(A), .B(B), .SEL(SEL), .Y(Y), .COUT(COUT),
  .sum(sum), .neg_b(neg_b), .twos_comp_b(twos_comp_b),

  .fa0_A(fa0.A), .fa0_B(fa0.B), .fa0_CIN(fa0.CIN), .fa0_SUM(fa0.SUM), .fa0_COUT(fa0.COUT),
  .fa1_A(fa1.A), .fa1_B(fa1.B), .fa1_CIN(fa1.CIN), .fa1_SUM(fa1.SUM), .fa1_COUT(fa1.COUT),
  .fa2_A(fa2.A), .fa2_B(fa2.B), .fa2_CIN(fa2.CIN), .fa2_SUM(fa2.SUM), .fa2_COUT(fa2.COUT),
  .fa3_A(fa3.A), .fa3_B(fa3.B), .fa3_CIN(fa3.CIN), .fa3_SUM(fa3.SUM), .fa3_COUT(fa3.COUT)
);