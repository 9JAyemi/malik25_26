// SVA for Voter: 3-input majority per bit
module Voter_sva #(parameter WIDTH = 1)(
  input  logic [(WIDTH-1):0] A, B, C,
  input  logic [(WIDTH-1):0] True
);

  // Sanity on parameter
  initial assert (WIDTH > 0) else $error("Voter WIDTH must be > 0");

  // Helper: popcount for three 1-bit values (only valid when inputs are 0/1)
  function automatic int pop3 (logic a, b, c);
    return (a ? 1 : 0) + (b ? 1 : 0) + (c ? 1 : 0);
  endfunction

  // Golden combinational equivalence (4-state): True == majority(A,B,C)
  assert property (@(A or B or C or True)
                   True === ((A & B) | (A & C) | (B & C)))
    else $error("Voter mismatch: True != majority(A,B,C)");

  // If inputs are all known, output must be known (no X/Z propagation)
  assert property (@(A or B or C)
                   (!$isunknown({A,B,C})) |-> (!$isunknown(True)))
    else $error("Voter produced X/Z on known inputs");

  // No spontaneous output changes without an input change
  assert property (@(A or B or C or True)
                   $stable({A,B,C}) |-> $stable(True))
    else $error("Voter output changed while inputs were stable");

  // Bit-wise properties and coverage
  genvar i;
  generate
    for (i = 0; i < WIDTH; i++) begin : bit_chk

      // If any two inputs are equal and known, True[i] must equal that value
      assert property (@(A[i] or B[i] or C[i])
                       (!$isunknown(A[i]) && !$isunknown(B[i]) && (A[i] === B[i]))
                       |-> (True[i] === A[i]))
        else $error("Voter[%0d]: A==B but True != A", i);

      assert property (@(A[i] or B[i] or C[i])
                       (!$isunknown(A[i]) && !$isunknown(C[i]) && (A[i] === C[i]))
                       |-> (True[i] === A[i]))
        else $error("Voter[%0d]: A==C but True != A", i);

      assert property (@(A[i] or B[i] or C[i])
                       (!$isunknown(B[i]) && !$isunknown(C[i]) && (B[i] === C[i]))
                       |-> (True[i] === B[i]))
        else $error("Voter[%0d]: B==C but True != B", i);

      // Functional coverage: exercise all 4 known input cardinalities per bit
      cover property (@(A[i] or B[i] or C[i])
                      (!$isunknown({A[i],B[i],C[i]})) && (pop3(A[i],B[i],C[i]) == 0));
      cover property (@(A[i] or B[i] or C[i])
                      (!$isunknown({A[i],B[i],C[i]})) && (pop3(A[i],B[i],C[i]) == 1));
      cover property (@(A[i] or B[i] or C[i])
                      (!$isunknown({A[i],B[i],C[i]})) && (pop3(A[i],B[i],C[i]) == 2));
      cover property (@(A[i] or B[i] or C[i])
                      (!$isunknown({A[i],B[i],C[i]})) && (pop3(A[i],B[i],C[i]) == 3));

      // Coverage: output toggles
      cover property (@(posedge True[i]) 1);
      cover property (@(negedge True[i]) 1);

      // Coverage: X-tolerance scenario (two known equal, third unknown)
      cover property (@(A[i] or B[i] or C[i])
                      ((A[i]===B[i] && !$isunknown(A[i]) && $isunknown(C[i])) ||
                       (A[i]===C[i] && !$isunknown(A[i]) && $isunknown(B[i])) ||
                       (B[i]===C[i] && !$isunknown(B[i]) && $isunknown(A[i]))));

    end
  endgenerate

endmodule

// Bind into DUT
bind Voter Voter_sva #(.WIDTH(WIDTH)) Voter_sva_i (.A(A), .B(B), .C(C), .True(True));