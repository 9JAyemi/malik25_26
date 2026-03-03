// SVA checker for RippleCarryAdder
// - Spec-level: behaves as a true 4-bit adder with carry-in/out
// - Concise, high-signal-coverage assertions and targeted coverpoints
// Provide a sampling clock from your environment when binding.

module RippleCarryAdder_sva (
  input logic         clk,
  input logic  [3:0]  A,
  input logic  [3:0]  B,
  input logic         Cin,
  input logic  [3:0]  S,
  input logic         Cout
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity: when inputs are known, outputs must be known
  assert property ( !$isunknown({A,B,Cin}) |-> !$isunknown({S,Cout}) )
    else $error("RCA: X/Z on outputs with known inputs");

  // Pure functional spec: 5-bit sum equals A + B + Cin
  assert property ( {Cout,S} == (A + B + Cin) )
    else $error("RCA: {Cout,S} != A + B + Cin");

  // Split checks (better debug granularity)
  assert property ( S    == (A + B + Cin)[3:0] )
    else $error("RCA: S mismatch vs low 4 bits of sum");
  assert property ( Cout == (A + B + Cin)[4] )
    else $error("RCA: Cout mismatch vs MSB of sum");

  // Combinational consistency: if inputs hold, outputs hold
  assert property ( $stable({A,B,Cin}) |-> $stable({S,Cout}) )
    else $error("RCA: outputs changed without input change");

  // Differential checks for Cin step behavior with A,B held
  assert property ( $stable(A) && $stable(B) && $rose(Cin)
                    |-> {Cout,S} == $past({Cout,S}) + 5'd1 )
    else $error("RCA: +1 increment on Cin rise violated");

  assert property ( $stable(A) && $stable(B) && $fell(Cin)
                    |-> {Cout,S} == $past({Cout,S}) - 5'd1 )
    else $error("RCA: -1 decrement on Cin fall violated");

  // Targeted functional coverage
  cover property ( A==4'h0 && B==4'h0 && Cin==1 && {Cout,S}==5'h01 );  // minimal +Cin
  cover property ( A==4'hF && B==4'hF && Cin==1 && {Cout,S}==5'h1F );  // maximal overflow
  cover property ( A==4'h8 && B==4'h8 && Cin==0 && {Cout,S}==5'h10 );  // MSB generate
  cover property ( A==4'hF && B==4'h0 && Cin==1 && {Cout,S}==5'h10 );  // full propagate
endmodule

// Bind into the DUT; provide a sampling clock from your environment
bind RippleCarryAdder RippleCarryAdder_sva u_rca_sva (
  .clk  (clk),         // drive from TB
  .A    (A),
  .B    (B),
  .Cin  (Cin),
  .S    (S),
  .Cout (Cout)
);