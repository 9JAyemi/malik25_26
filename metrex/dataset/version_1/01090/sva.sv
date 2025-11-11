// SVA for xor_gate: concise, full functional and structural checks with coverage.
// Bind into the DUT to access internal nets.
module xor_gate_sva (
    input  logic A,
    input  logic B,
    input  logic X,
    input  logic VPWR,
    input  logic VGND,
    input  logic not_A,
    input  logic not_B,
    input  logic A_and_not_B,
    input  logic not_A_and_B
);

    // Power-good gating
    logic pwr_good;
    assign pwr_good = (VPWR === 1'b1) && (VGND === 1'b0);

    // Optional: flag any change on power rails that violates tie-offs
    ap_pwr_tied: assert property (@(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
                                  (VPWR === 1'b1 && VGND === 1'b0))
      else $error("xor_gate: Power rails not tied correctly");

    // Functional XOR when inputs are known and power good
    ap_xor: assert property (@(posedge A or negedge A or posedge B or negedge B or
                               posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
                             disable iff (!pwr_good)
                             (!$isunknown({A,B})) |-> (X == (A ^ B)))
      else $error("xor_gate: X != A ^ B");

    // Structural decomposition matches
    ap_notA: assert property (@(posedge A or negedge A or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
                              disable iff (!pwr_good)
                              (!$isunknown(A)) |-> (not_A == ~A))
      else $error("xor_gate: not_A != ~A");

    ap_notB: assert property (@(posedge B or negedge B or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
                              disable iff (!pwr_good)
                              (!$isunknown(B)) |-> (not_B == ~B))
      else $error("xor_gate: not_B != ~B");

    ap_and1: assert property (@(posedge A or negedge A or posedge B or negedge B or
                                posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
                              disable iff (!pwr_good)
                              (!$isunknown({A,B})) |-> (A_and_not_B == (A & ~B)))
      else $error("xor_gate: A_and_not_B mismatch");

    ap_and2: assert property (@(posedge A or negedge A or posedge B or negedge B or
                                posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
                              disable iff (!pwr_good)
                              (!$isunknown({A,B})) |-> (not_A_and_B == (~A & B)))
      else $error("xor_gate: not_A_and_B mismatch");

    ap_or: assert property (@(posedge A or negedge A or posedge B or negedge B or
                              posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
                            disable iff (!pwr_good)
                            (!$isunknown({A,B})) |-> (X == (A_and_not_B | not_A_and_B)))
      else $error("xor_gate: OR combine mismatch");

    // Mutually exclusive product terms (no overlap)
    ap_mut_excl: assert property (@(posedge A or negedge A or posedge B or negedge B or
                                    posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
                                  disable iff (!pwr_good)
                                  !(A_and_not_B && not_A_and_B))
      else $error("xor_gate: Overlap in product terms");

    // No unknowns on outputs/internals when inputs are known
    ap_known_out: assert property (@(posedge A or negedge A or posedge B or negedge B)
                                   disable iff (!pwr_good)
                                   (!$isunknown({A,B})) |-> (!$isunknown(X)))
      else $error("xor_gate: X is X/Z with known inputs");

    ap_known_ints: assert property (@(posedge A or negedge A or posedge B or negedge B)
                                    disable iff (!pwr_good)
                                    (!$isunknown({A,B})) |-> (!$isunknown({not_A,not_B,A_and_not_B,not_A_and_B})))
      else $error("xor_gate: Internal nets are X/Z with known inputs");

    // Coverage: all input combinations observed with correct X
    cp_00: cover property (@(posedge A or negedge A or posedge B or negedge B)
                           disable iff (!pwr_good)
                           (A==1'b0 && B==1'b0 && X==1'b0));

    cp_01: cover property (@(posedge A or negedge A or posedge B or negedge B)
                           disable iff (!pwr_good)
                           (A==1'b0 && B==1'b1 && X==1'b1));

    cp_10: cover property (@(posedge A or negedge A or posedge B or negedge B)
                           disable iff (!pwr_good)
                           (A==1'b1 && B==1'b0 && X==1'b1));

    cp_11: cover property (@(posedge A or negedge A or posedge B or negedge B)
                           disable iff (!pwr_good)
                           (A==1'b1 && B==1'b1 && X==1'b0));

    // Coverage: each product term asserts at least once; X toggles both ways
    cp_term1: cover property (@(posedge A or negedge A or posedge B or negedge B)
                              disable iff (!pwr_good) A_and_not_B);

    cp_term2: cover property (@(posedge A or negedge A or posedge B or negedge B)
                              disable iff (!pwr_good) not_A_and_B);

    cp_x_rise: cover property (@(posedge A or negedge A or posedge B or negedge B)
                               disable iff (!pwr_good) $rose(X));

    cp_x_fall: cover property (@(posedge A or negedge A or posedge B or negedge B)
                               disable iff (!pwr_good) $fell(X));

endmodule

// Bind into the DUT (connects to internal nets by name in xor_gate scope)
bind xor_gate xor_gate_sva sva_xor_gate (
    .A(A),
    .B(B),
    .X(X),
    .VPWR(VPWR),
    .VGND(VGND),
    .not_A(not_A),
    .not_B(not_B),
    .A_and_not_B(A_and_not_B),
    .not_A_and_B(not_A_and_B)
);