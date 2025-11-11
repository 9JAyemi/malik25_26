// SVA for mux_2_to_1
// Bind this file to the DUT. Focuses on correctness, X-safety, and concise coverage.

module mux_2_to_1_sva (
  input logic A,
  input logic B,
  input logic S,
  input logic Y
);

  // Core functional equivalence to an X-accurate mux
  // Flags X-optimism if S is X and A!=B.
  ap_func: assert property (@(A or B or S)
    Y === (S ? B : A)
  ) else $error("mux_2_to_1: Y != (S?B:A)");

  // Path-specific immediate response
  ap_path_A: assert property (@(A)
    (S === 0) |-> ##0 (Y === A)
  ) else $error("mux_2_to_1: Y did not follow A when S==0");

  ap_path_B: assert property (@(B)
    (S === 1) |-> ##0 (Y === B)
  ) else $error("mux_2_to_1: Y did not follow B when S==1");

  // Y should only change when at least one input changes
  ap_y_change_cause: assert property (@(Y)
    $changed(A) || $changed(B) || $changed(S)
  ) else $error("mux_2_to_1: Y changed without input change");

  // Cleanliness: no unknown select; if all inputs known, Y must be known
  ap_no_x_sel: assert property (@(A or B or S)
    !$isunknown(S)
  ) else $error("mux_2_to_1: Select S is X/Z");

  ap_known_out_when_known_in: assert property (@(A or B or S)
    (!$isunknown({A,B,S})) |-> !$isunknown(Y)
  ) else $error("mux_2_to_1: Y is X/Z while A,B,S are known");

  // Degenerate case: when A==B, Y must equal that value regardless of S
  ap_degenerate: assert property (@(A or B or S)
    (A === B) |-> ##0 (Y === A)
  ) else $error("mux_2_to_1: Y != A when A==B");

  // Coverage: exercise both paths and select toggles with visible effect
  cp_sel0_path:  cover property (@(A) (S===0) && $changed(A) && (Y===A));
  cp_sel1_path:  cover property (@(B) (S===1) && $changed(B) && (Y===B));
  cp_s_rise:     cover property (@(posedge S) (A!==B) && (Y===B));
  cp_s_fall:     cover property (@(negedge S) (A!==B) && (Y===A));
  cp_seen_sel0:  cover property (@(S) S===0);
  cp_seen_sel1:  cover property (@(S) S===1);

endmodule

bind mux_2_to_1 mux_2_to_1_sva u_mux_2_to_1_sva (.A(A), .B(B), .S(S), .Y(Y));