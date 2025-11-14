// SVA for ripple_carry_adder
// Bind this file alongside the DUT

module ripple_carry_adder_sva (
  input logic        clk,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic        C_in,
  input logic [3:0]  S,
  input logic        C_out
);

  // Establish safe $past() usage
  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Functional correctness: registered outputs equal previous-cycle 5-bit sum
  property p_sum_ok;
    {C_out, S} == $past(A) + $past(B) + $past(C_in);
  endproperty
  assert property (p_sum_ok)
    else $error("Adder mismatch: exp=%0d got=%0d (A=%0d B=%0d Cin=%0b)",
                $past(A)+$past(B)+$past(C_in), {C_out,S}, $past(A), $past(B), $past(C_in));

  // Outputs never X/Z after first valid cycle
  assert property (!$isunknown({S,C_out}));

  // Outputs only change on clock edges (approximate no-glitch check)
  assert property (@(negedge clk) $stable(S) && $stable(C_out));

  // Coverage: no-carry and carry-out cases
  cover property ( ($past(A)+$past(B)+$past(C_in)) < 16 );
  cover property ( ($past(A)+$past(B)+$past(C_in)) >= 16 );

  // Corner cases
  cover property ( $past(A)==4'h0 && $past(B)==4'h0 && $past(C_in)==1'b0 );
  cover property ( $past(A)==4'hF && $past(B)==4'hF && $past(C_in)==1'b1 );

  // Carry due to lower-bit propagate (not MSB generate)
  cover property ( (($past(A)+$past(B)+$past(C_in)) >= 16) && ($past(A[3] & B[3])==1'b0) );

endmodule

bind ripple_carry_adder ripple_carry_adder_sva sva_bind (
  .clk(clk),
  .A(A),
  .B(B),
  .C_in(C_in),
  .S(S),
  .C_out(C_out)
);