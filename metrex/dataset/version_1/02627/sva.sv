// SVA checker and bind for pipelined_ripple_carry_adder
module pipelined_ripple_carry_adder_sva;

  // Access bound instance signals directly
  default clocking cb @(posedge clk); endclocking

  // Past-valid shift for 1/2/3-cycle lookbacks
  logic [2:0] pv;
  initial pv = 3'b000;
  always_ff @(posedge clk) pv <= {pv[1:0], 1'b1};

  function automatic logic maj3 (logic a,b,c);
    return (a & b) | ((a | b) & c);
  endfunction

  // Helper to form 5-bit sum (carry + 4-bit sum)
  function automatic logic [4:0] sum5 (logic [3:0] x, logic [3:0] y, logic cin);
    return {1'b0,x} + {1'b0,y} + cin;
  endfunction

  // Basic sanity: inputs/outputs known when used
  assert property (!$isunknown({A,B,Cin}));
  assert property (pv[2] |-> !$isunknown({V,S}));

  // Stage-1 correctness
  assert property (P1_S == sum5(A,B,Cin)[3:0]);
  assert property (P1_C == maj3(A[0], B[0], Cin));

  // Stage-2 pipeline and carry logic
  assert property (pv[0] |-> P2_S == $past(P1_S));
  assert property (pv[0] |-> P2_C == maj3($past(P1_S[0]), $past(P1_C), $past(P1_S[1])));

  // Stage-3 pipeline and carry logic
  assert property (pv[1] |-> P3_S == $past(P2_S));
  assert property (pv[1] |-> P3_C == maj3($past(P2_S[1]), $past(P2_C), $past(P2_S[2])));

  // Output stage registers
  assert property (pv[2] |-> S == $past(P3_S));
  assert property (pv[2] |-> V == $past(P3_C));

  // End-to-end functional check: 3-cycle latency add
  assert property (pv[2] |-> {V,S} == $past(sum5(A,B,Cin), 3));

  // Minimal but meaningful coverage
  cover property (pv[2] && V);          // carry/overflow observed
  cover property (pv[2] && !V);
  cover property (pv[2] && (S == 4'h0));
  cover property (pv[2] && (S == 4'hF));
  cover property (pv[0] && P1_C);
  cover property (pv[1] && P2_C);
  cover property (pv[2] && P3_C);

endmodule

bind pipelined_ripple_carry_adder pipelined_ripple_carry_adder_sva sva_inst();