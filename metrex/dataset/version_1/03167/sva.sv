// SVA for and4 — concise, high-quality checks and coverage
module and4_sva (
  input logic A, B, C, D,
  input logic Y,
  input logic w1, w2, w3
);

  // Functional equivalence (only when inputs known)
  assert property (@(A or B or C or D or Y)
                   !$isunknown({A,B,C,D}) |-> Y === (A & B & C & D));

  // Internal decomposition correctness (guarded against Xs)
  assert property (@(A or B or w1) !$isunknown({A,B})   |-> w1 === (A & B));
  assert property (@(C or D or w2) !$isunknown({C,D})   |-> w2 === (C & D));
  assert property (@(w1 or w2 or w3) !$isunknown({w1,w2}) |-> w3 === (w1 & w2));
  assert property (@(Y or w3)       !$isunknown(w3)     |-> Y  === w3);

  // Output cannot be 1 unless all inputs are 1
  assert property (@(A or B or C or D or Y) (Y === 1'b1) |-> (A && B && C && D));

  // Each input controls Y when the other three are 1
  assert property (@(A or B or C or D or Y) (B && C && D && !$isunknown({A,B,C,D})) |-> (Y === A));
  assert property (@(A or B or C or D or Y) (A && C && D && !$isunknown({A,B,C,D})) |-> (Y === B));
  assert property (@(A or B or C or D or Y) (A && B && D && !$isunknown({A,B,C,D})) |-> (Y === C));
  assert property (@(A or B or C or D or Y) (A && B && C && !$isunknown({A,B,C,D})) |-> (Y === D));

  // No X on Y when inputs are all known
  assert property (@(A or B or C or D or Y) !$isunknown({A,B,C,D}) |-> !$isunknown(Y));

  // Coverage: observe both output values
  cover property (@(A or B or C or D or Y) Y === 1'b0);
  cover property (@(A or B or C or D or Y) Y === 1'b1);

  // Coverage: all 16 input combinations seen at least once
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cv_all_inputs
      cover property (@(A or B or C or D) {A,B,C,D} === i[3:0]);
    end
  endgenerate

  // Coverage: internal nodes can assert
  cover property (@(A or B) w1 === 1'b1);
  cover property (@(C or D) w2 === 1'b1);
  cover property (@(w1 or w2 or w3) w3 === 1'b1);

endmodule

// Bind the SVA to the DUT (gains access to internal nets w1/w2/w3)
bind and4 and4_sva u_and4_sva (.A(A), .B(B), .C(C), .D(D), .Y(Y), .w1(w1), .w2(w2), .w3(w3));