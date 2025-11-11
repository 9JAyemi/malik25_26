// SVA for sky130_fd_sc_hdll__nor2b: Y = (~A) & B_N
// Quality-focused, concise checks + functional coverage

module sky130_fd_sc_hdll__nor2b_sva (
  input logic A,
  input logic B_N,
  input logic Y,
  input logic not0_out,
  input logic and0_out_Y
);

  // Top-level function: when inputs are known, Y must be known and correct
  assert property (@(A or B_N or Y)
    ! $isunknown({A,B_N}) |-> ##0 (Y === ((~A) & B_N))
  );

  // Strengthened constant-result cases (handle X on the other input)
  assert property (@(A or B_N or Y) (A   === 1'b1) |-> ##0 (Y === 1'b0));
  assert property (@(A or B_N or Y) (B_N === 1'b0) |-> ##0 (Y === 1'b0));
  assert property (@(A or B_N or Y) (A===1'b0 && B_N===1'b1) |-> ##0 (Y === 1'b1));

  // Output only changes when an input changes (no spurious glitches)
  assert property (@(A or B_N or Y) $changed(Y) |-> ($changed(A) || $changed(B_N)));

  // Structural conformance of internal nets
  assert property (@(A or not0_out)           ##0 (not0_out   === ~A));
  assert property (@(not0_out or B_N or and0_out_Y) ##0 (and0_out_Y === (not0_out & B_N)));
  assert property (@(and0_out_Y or Y)         ##0 (Y          === and0_out_Y));

  // Functional truth-table coverage (all 4 input combos with expected Y)
  cover property (@(A or B_N or Y) (A===0 && B_N===0) ##0 (Y===0));
  cover property (@(A or B_N or Y) (A===0 && B_N===1) ##0 (Y===1));
  cover property (@(A or B_N or Y) (A===1 && B_N===0) ##0 (Y===0));
  cover property (@(A or B_N or Y) (A===1 && B_N===1) ##0 (Y===0));

  // Edge coverage on Y and cause-effect coverage
  cover property (@(A or B_N or Y) $rose(Y));
  cover property (@(A or B_N or Y) $fell(Y));
  cover property (@(A or B_N or Y) ($fell(A) && B_N===1) ##0 $rose(Y));
  cover property (@(A or B_N or Y) ($rose(B_N) && A===0) ##0 $rose(Y));
  cover property (@(A or B_N or Y) ($rose(A) && B_N===1) ##0 $fell(Y));
  cover property (@(A or B_N or Y) ($fell(B_N) && A===0) ##0 $fell(Y));

endmodule

// Bind into the DUT (accessing internal nets)
bind sky130_fd_sc_hdll__nor2b sky130_fd_sc_hdll__nor2b_sva
  nor2b_chk (.A(A), .B_N(B_N), .Y(Y), .not0_out(not0_out), .and0_out_Y(and0_out_Y));