// SVA checker for comparator
module comparator_sva(input logic [15:0] A, input logic [15:0] B, input logic out);

  // Fundamental combinational equivalence (race-safe with ##0)
  property p_out_eq_gt; out === (A > B); endproperty
  assert property (@(A or B or out) ##0 p_out_eq_gt)
    else $error("comparator: out != (A > B). A=%0h B=%0h out=%0b", A, B, out);

  // No spurious output change without input change
  assert property (@(A or B or out) $stable({A,B}) |-> $stable(out))
    else $error("comparator: out changed without A/B change. A=%0h B=%0h", A, B);

  // Output never X/Z
  assert property (@(A or B or out) !$isunknown(out))
    else $error("comparator: out is X/Z. A=%0h B=%0h out=%b", A, B, out);

  // With known inputs, equivalence must hold
  assert property (@(A or B or out) ##0 (!$isunknown({A,B})) |-> (out === (A > B)))
    else $error("comparator: known inputs but out != (A>B). A=%0h B=%0h out=%0b", A, B, out);

  // Functional coverage
  cover property (@(A or B or out) ##0 ((A > B) &&  out));
  cover property (@(A or B or out) ##0 ((A < B) && !out));
  cover property (@(A or B or out) ##0 ((A == B) && !out));

  // Corner coverage
  cover property (@(A or B or out) ##0 (A==16'hFFFF && B==16'h0000 &&  out));
  cover property (@(A or B or out) ##0 (A==16'h0000 && B==16'hFFFF && !out));

endmodule

// Bind into DUT
bind comparator comparator_sva u_comparator_sva(.A(A), .B(B), .out(out));