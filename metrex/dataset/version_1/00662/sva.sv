// SVA checker for sky130_fd_sc_ls__and4
module and4_sva (
  input logic A, B, C, D, X
);
  default clocking cb @(*) endclocking

  // Functional correctness (4-state accurate)
  ap_and_truth: assert property (X === (A & B & C & D));

  // No spurious output changes (output changes only when some input changes)
  ap_no_spurious: assert property ($changed(X) |-> $changed({A,B,C,D}));

  // Determinism when inputs are all known
  ap_known_inputs: assert property (
    ! $isunknown({A,B,C,D}) |-> (! $isunknown(X) && (X == (A & B & C & D)))
  );

  // Coverage: all 16 known input combinations
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cv_inputs
      cover property ({A,B,C,D} === i[3:0]);
    end
  endgenerate

  // Coverage: output transitions
  cv_x_rise: cover property ($rose(X));
  cv_x_fall: cover property ($fell(X));

  // Coverage: unknown propagation case (no 0s, some X/Z on inputs -> X unknown)
  cv_xprop: cover property (
    (A!==1'b0 && B!==1'b0 && C!==1'b0 && D!==1'b0) &&
    $isunknown({A,B,C,D}) && $isunknown(X)
  );
endmodule

// Bind into DUT
bind sky130_fd_sc_ls__and4 and4_sva u_and4_sva(.A(A), .B(B), .C(C), .D(D), .X(X));