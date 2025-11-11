// SVA checker for comparator_4bit
module comparator_4bit_sva (
  input [3:0] A,
  input [3:0] B,
  input       EQ
);
  // Sample on any relevant signal change; check after zero-delay settle
  default clocking cb @(A or B or EQ); endclocking

  // Functional correctness: EQ reflects Verilog if-semantics of (A == B)
  // True case: when (A==B) evaluates to 1, EQ must be 1
  assert property ( ((A == B) === 1'b1) |-> ##0 (EQ === 1'b1) )
    else $error("EQ must be 1 when (A==B) is 1");
  // All other cases (0 or X): EQ must be 0
  assert property ( ((A == B) !== 1'b1) |-> ##0 (EQ === 1'b0) )
    else $error("EQ must be 0 when (A==B) is 0 or X");

  // Output must never be X/Z
  assert property ( 1 |-> ##0 !$isunknown(EQ) )
    else $error("EQ must never be X/Z");

  // Coverage: equal and not-equal cases observed and correctly reflected
  cover property ( ((A == B) === 1'b1) ##0 (EQ === 1'b1) );
  cover property ( ((A == B) !== 1'b1) ##0 (EQ === 1'b0) );
  // Exercise both output transitions
  cover property ( $rose(EQ) );
  cover property ( $fell(EQ) );
  // A few boundary examples
  cover property ( (A==4'h0 && B==4'h0) ##0 (EQ==1) );
  cover property ( (A==4'hF && B==4'hF) ##0 (EQ==1) );
  cover property ( (A==4'h0 && B==4'hF) ##0 (EQ==0) );
  cover property ( (A==4'hF && B==4'h0) ##0 (EQ==0) );
endmodule

// Bind into DUT
bind comparator_4bit comparator_4bit_sva u_comparator_4bit_sva (.*);