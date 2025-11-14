// SVA for comparator: Y must be absolute difference |A-B|
// Bind into the DUT
bind comparator comparator_sva u_comparator_sva (.*);

module comparator_sva
(
  input logic [3:0] A,
  input logic [3:0] B,
  input logic [3:0] Y
);

  // Functional correctness: absolute difference
  assert property (@(A or B or Y)
    Y == ((A >= B) ? (A - B) : (B - A))
  ) else $error("Y != |A-B|: A=%0d B=%0d Y=%0d", A, B, Y);

  // Equal case explicitly zero
  assert property (@(A or B or Y)
    (A == B) |-> (Y == 4'd0)
  ) else $error("A==B but Y!=0: A=%0d B=%0d Y=%0d", A, B, Y);

  // No X/Z on output when inputs are 2-state
  assert property (@(A or B or Y)
    (!$isunknown({A,B})) |-> !$isunknown(Y)
  ) else $error("Y unknown while inputs 2-state: A=%b B=%b Y=%b", A, B, Y);

  // Combinational stability: Y changes only when A or B changes
  assert property (@(A or B or Y)
    $changed(Y) |-> ($changed(A) || $changed(B))
  ) else $error("Y changed without A/B change: A=%0d B=%0d Y=%0d", A, B, Y);

  // Basic branch coverage
  cover property (@(A or B) (A >  B) && (Y == (A - B)));
  cover property (@(A or B) (B >  A) && (Y == (B - A)));
  cover property (@(A or B) (A == B) && (Y == 4'd0));

  // Boundary coverage
  cover property (@(A or B) (A == 4'd0)  && (B == 4'd0)  && (Y == 4'd0));
  cover property (@(A or B) (A == 4'd15) && (B == 4'd15) && (Y == 4'd0));
  cover property (@(A or B) (A == 4'd0)  && (B == 4'd15) && (Y == 4'd15));
  cover property (@(A or B) (A == 4'd15) && (B == 4'd0)  && (Y == 4'd15));

  // Exercise all possible output magnitudes 0..15
  genvar d;
  generate
    for (d = 0; d < 16; d++) begin : cov_diff_all
      cover property (@(A or B)
        (Y == d) &&
        (((A >= B) && (A - B == d)) || ((B > A) && (B - A == d)))
      );
    end
  endgenerate

endmodule