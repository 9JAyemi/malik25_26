module sky130_fd_sc_hd__o21a_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic X,
    input logic Y,
    input logic Z,
    input logic W
);
    ///// Functional definitions /////
    // X must equal A1 AND A2.
    check_x_and_def: assert property (
        @(posedge A1) X == (A1 & A2)
    );
    // Y must equal A1 OR A2.
    check_y_or_def: assert property (
        @(posedge A1) Y == (A1 | A2)
    );
    // Z must equal A1 XOR A2.
    check_z_xor_def: assert property (
        @(posedge A1) Z == (A1 ^ A2)
    );
    // W must equal B1 AND VPWR.
    check_w_and_def: assert property (
        @(posedge B1) W == (B1 & VPWR)
    );

    ///// Output relationships implied by the logic /////
    // If X is 1, Y must be 1.
    check_x_implies_y: assert property (
        @(posedge A1) X |-> Y
    );
    // If X is 1, Z must be 0.
    check_x_implies_not_z: assert property (
        @(posedge A1) X |-> (Z == 1'b0)
    );
    // If Z is 1, X must be 0.
    check_z_implies_not_x: assert property (
        @(posedge A1) Z |-> (X == 1'b0)
    );
    // If Z is 1, Y must be 1.
    check_z_implies_y: assert property (
        @(posedge A1) Z |-> Y
    );
    // Y equals X OR Z (OR decomposition).
    check_y_equals_x_or_z: assert property (
        @(posedge A1) Y == (X | Z)
    );
    // X and Z are mutually exclusive.
    check_x_and_z_disjoint: assert property (
        @(posedge A1) (X & Z) == 1'b0
    );

    ///// Power gating behavior for W /////
    // W can be 1 only if B1 is 1.
    check_w_requires_b1: assert property (
        @(posedge A1) W |-> B1
    );
    // W can be 1 only if VPWR is 1.
    check_w_requires_vpwr: assert property (
        @(posedge A1) W |-> VPWR
    );
    // If VPWR is 0 then W must be 0.
    check_vpwr_low_forces_w_low: assert property (
        @(posedge A1) (!VPWR) |-> (W == 1'b0)
    );

    ///// Sanity on specific input combinations /////
    // When A1 and A2 are both 1: X=1, Y=1, Z=0.
    check_both_one: assert property (
        @(posedge A1) (A1 & A2) |-> (X && Y && (Z == 1'b0))
    );
    // When A1 and A2 differ: Z=1, Y=1, X=0.
    check_inputs_differ: assert property (
        @(posedge A1) (A1 ^ A2) |-> (Z && Y && (X == 1'b0))
    );
endmodule