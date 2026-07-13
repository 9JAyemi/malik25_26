module nand4x1_sva (
    input logic Z,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);
    // Z equals (A&B) OR (C&D).
    check_functional_equivalence: assert property (
        @(posedge $global_clock) Z == ((A & B) | (C & D))
    );

    // When A and B are both 1, Z must be 1.
    check_ab_implies_z: assert property (
        @(posedge $global_clock) (A & B) |-> (Z == 1'b1)
    );

    // When C and D are both 1, Z must be 1.
    check_cd_implies_z: assert property (
        @(posedge $global_clock) (C & D) |-> (Z == 1'b1)
    );

    // If neither (A&B) nor (C&D) is 1, Z must be 0.
    check_pairs_low_implies_z_low: assert property (
        @(posedge $global_clock) (!(A & B) && !(C & D)) |-> (Z == 1'b0)
    );

    // If Z is 0, both (A&B) and (C&D) must be 0.
    check_z_low_implies_pairs_low: assert property (
        @(posedge $global_clock) (Z == 1'b0) |-> (!(A & B) && !(C & D))
    );

    // If inputs are stable across a cycle, Z remains stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge $global_clock) ($stable(A) && $stable(B) && $stable(C) && $stable(D)) |-> $stable(Z)
    );

    // A==0 and C==0 guarantee Z==0.
    check_ac_zero_implies_z_zero: assert property (
        @(posedge $global_clock) ((A == 1'b0) && (C == 1'b0)) |-> (Z == 1'b0)
    );

    // A==0 and D==0 guarantee Z==0.
    check_ad_zero_implies_z_zero: assert property (
        @(posedge $global_clock) ((A == 1'b0) && (D == 1'b0)) |-> (Z == 1'b0)
    );

    // B==0 and C==0 guarantee Z==0.
    check_bc_zero_implies_z_zero: assert property (
        @(posedge $global_clock) ((B == 1'b0) && (C == 1'b0)) |-> (Z == 1'b0)
    );

    // B==0 and D==0 guarantee Z==0.
    check_bd_zero_implies_z_zero: assert property (
        @(posedge $global_clock) ((B == 1'b0) && (D == 1'b0)) |-> (Z == 1'b0)
    );
endmodule