// Checker for module adder. Note: C is 4-bit; {carry,sum} truncates to sum[3:0].
module adder_sva(input logic [3:0] A, B, input logic sel, input logic [3:0] C);

  // Functional correctness: C is sum or bitwise-not of sum (carry is dropped by truncation)
  assert property (@(*) disable iff ($isunknown({A,B,sel}))
    C == (sel ? ~((A+B)[3:0]) : ((A+B)[3:0]))
  );

  // Carry-out correctness vs canonical formula
  assert property (@(*) disable iff ($isunknown({A,B}))
    (((A+B) > 4'd15)) == ((A[3] & B[3]) | (A[3] & ~((A+B)[3])) | (B[3] & ~((A+B)[3])))
  );

  // No X/Z on output when inputs are known
  assert property (@(*) disable iff ($isunknown({A,B,sel}))
    !$isunknown(C)
  );

  // Toggling sel with stable A,B inverts C
  assert property (@(posedge sel or negedge sel) disable iff ($isunknown({A,B,sel,C}))
    $stable(A) && $stable(B) |-> C == ~ $past(C)
  );

  // Coverage: both sel values with/without carry, plus corners
  cover property (@(*) ! $isunknown({A,B,sel}) && (sel==0) && ((A+B) < 16) && (C == ((A+B)[3:0])));
  cover property (@(*) ! $isunknown({A,B,sel}) && (sel==0) && ((A+B) > 15) && (C == ((A+B)[3:0])));
  cover property (@(*) ! $isunknown({A,B,sel}) && (sel==1) && ((A+B) < 16) && (C == ~((A+B)[3:0])));
  cover property (@(*) ! $isunknown({A,B,sel}) && (sel==1) && ((A+B) > 15) && (C == ~((A+B)[3:0])));
  cover property (@(*) A==4'h0 && B==4'h0 && sel==0 && C==4'h0);
  cover property (@(*) A==4'hF && B==4'hF && sel==0 && C==4'hE);

endmodule

bind adder adder_sva u_adder_sva(.A(A), .B(B), .sel(sel), .C(C));