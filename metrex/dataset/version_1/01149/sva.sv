// SVA for bitwise_op. Bind this file; no DUT edits needed.

module bitwise_op_sva (
  input  logic [7:0] A, B,
  input  logic [1:0] C,
  input  logic [7:0] out
);

  // Functional correctness (all modes), X-gated, 0-delay settle
  assert property (@(A or B or C)
    !$isunknown({A,B,C}) |-> ##0
      (out == (C==2'b00 ? (A & B) :
               C==2'b01 ? (A | B) :
               C==2'b10 ? (A ^ B) :
                          ~(A ^ B)))
  );

  // Per-mode checks (debug-friendly)
  assert property (@(A or B or C)
    (!$isunknown({A,B,C}) && C==2'b00) |-> ##0 (out == (A & B)));
  assert property (@(A or B or C)
    (!$isunknown({A,B,C}) && C==2'b01) |-> ##0 (out == (A | B)));
  assert property (@(A or B or C)
    (!$isunknown({A,B,C}) && C==2'b10) |-> ##0 (out == (A ^ B)));
  assert property (@(A or B or C)
    (!$isunknown({A,B,C}) && C==2'b11) |-> ##0 (out == ~(A ^ B)));

  // Output must be 2-state when inputs are 2-state
  assert property (@(A or B or C)
    !$isunknown({A,B,C}) |-> ##0 !$isunknown(out)
  );

  // Select must be 2-state (prevents latch-like behavior on X/Z select)
  assert property (@(A or B or C or out) !$isunknown(C));

  // No spurious output changes without input/select change
  assert property (@(out) $stable({A,B,C}) |-> 0);

  // Coverage: exercise each mode with correct result
  cover property (@(A or B or C) (C==2'b00) ##0 (out == (A & B)));
  cover property (@(A or B or C) (C==2'b01) ##0 (out == (A | B)));
  cover property (@(A or B or C) (C==2'b10) ##0 (out == (A ^ B)));
  cover property (@(A or B or C) (C==2'b11) ##0 (out == ~(A ^ B)));

  // Compact sanity value coverage
  cover property (@(A or B or C) (C==2'b10) && (A==8'hAA) && (B==8'h55) ##0 (out==8'hFF));
  cover property (@(A or B or C) (C==2'b11) && (A==8'hAA) && (B==8'h55) ##0 (out==8'h00));
  cover property (@(A or B or C) (C==2'b00) && (A==8'hFF) && (B==8'h0F) ##0 (out==8'h0F));
  cover property (@(A or B or C) (C==2'b01) && (A==8'hF0) && (B==8'h0F) ##0 (out==8'hFF));

endmodule

bind bitwise_op bitwise_op_sva sva_bitwise_op (.A(A), .B(B), .C(C), .out(out));