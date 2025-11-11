// SVA for ripple_carry_adder
// Drop-in bind; checks functional correctness, internal carry chain, and key corner cases.
// Clockless concurrent assertions (evaluate on any activity).

bind ripple_carry_adder rca_sva_chk();

module rca_sva_chk;

  // Golden expectations (pure-combinational)
  logic [4:0] exp_sum;
  logic [3:0] exp_carry;

  always_comb begin
    exp_sum = A + B + Cin;
    exp_carry[0] = (A[0] & B[0]) | (Cin & (A[0] ^ B[0]));
    for (int i = 1; i < 4; i++) begin
      exp_carry[i] = (A[i] & B[i]) | (exp_carry[i-1] & (A[i] ^ B[i]));
    end
  end

  // Helper for gating on known inputs
  function automatic bit known_inputs(); return !$isunknown({A,B,Cin}); endfunction

  // Functional correctness (golden)
  assert property ( known_inputs() |-> {Cout, S} == exp_sum )
    else $error("Adder result mismatch: A=%0h B=%0h Cin=%0b got {Cout,S}=%0h exp=%0h",
                A, B, Cin, {Cout,S}, exp_sum);

  // Structural consistency and bit-level checks
  assert property ( known_inputs() |-> S == sum )
    else $error("S not equal to internal sum");

  assert property ( known_inputs() |-> Cout == carry[3] )
    else $error("Cout not equal to carry[3]");

  // Correct carry chain for a true ripple-carry adder
  assert property ( known_inputs() |-> carry[0] == ((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))) )
    else $error("carry[0] incorrect");

  genvar gi;
  generate
    for (gi = 1; gi < 4; gi++) begin : g_carry_chk
      assert property ( known_inputs() |-> carry[gi] ==
                        ((A[gi] & B[gi]) | (carry[gi-1] & (A[gi] ^ B[gi]))) )
        else $error("carry[%0d] incorrect", gi);
    end
  endgenerate

  // Sum bit correctness with proper carry-in
  assert property ( known_inputs() |-> S[0] == (A[0] ^ B[0] ^ Cin) )
    else $error("S[0] incorrect");

  assert property ( known_inputs() |-> S[3:1] ==
                    ((A[3:1] ^ B[3:1]) ^ exp_carry[2:0]) )
    else $error("S[3:1] incorrect");

  // Commutativity sanity check
  assert property ( known_inputs() |-> (A + B + Cin) == (B + A + Cin) )
    else $error("Commutativity violated");

  // Known-ness checks
  assert property ( !$isunknown({S,Cout}) )
    else $error("Outputs contain X/Z");

  // Coverage: basic, overflow, full propagate, mixed
  cover property ( A==4'h0 && B==4'h0 && Cin==1'b0 && {Cout,S}==5'h00 );
  cover property ( A==4'hF && B==4'hF && Cin==1'b0 && Cout==1'b1 && S==4'hE );
  cover property ( A==4'hF && B==4'h0 && Cin==1'b1 && Cout==1'b1 && S==4'h0 ); // full propagate
  cover property ( A==4'hA && B==4'h5 && Cin==1'b1 ); // mixed generate/propagate/kill

  // Ensure each internal carry bit can assert
  cover property ( carry[0] );
  cover property ( carry[1] );
  cover property ( carry[2] );
  cover property ( carry[3] );

endmodule