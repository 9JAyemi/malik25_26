module logic_gate_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Y,
    // Exposed internal nets from RTL for structural checks
    input logic and0_out,
    input logic not0_out,
    input logic not1_out,
    input logic and1_out,
    input logic or0_out
);
    // No clock or reset in RTL; pure combinational. Assertions are sampled on posedges of A/B/C.

    ///// Functional equivalence (sampled on multiple inputs) /////
    // Y equals (A&B) | (B&C) when sampled on A.
    check_y_sop_on_A: assert property (
        @(posedge A) Y == ((A & B) | (B & C))
    );
    // Y equals (A&B) | (B&C) when sampled on B.
    check_y_sop_on_B: assert property (
        @(posedge B) Y == ((A & B) | (B & C))
    );
    // Y equals (A&B) | (B&C) when sampled on C.
    check_y_sop_on_C: assert property (
        @(posedge C) Y == ((A & B) | (B & C))
    );
    // Y equals B & (A | C) when sampled on A.
    check_y_factored_on_A: assert property (
        @(posedge A) Y == (B & (A | C))
    );

    ///// Structural gate-level consistency /////
    // and0 implements A & B.
    check_and0_definition: assert property (
        @(posedge A) and0_out == (A & B)
    );
    // not0 implements ~B.
    check_not0_definition: assert property (
        @(posedge A) not0_out == ~B
    );
    // not1 implements inversion of not0.
    check_not1_definition: assert property (
        @(posedge A) not1_out == ~not0_out
    );
    // and1 implements not1_out & C.
    check_and1_definition: assert property (
        @(posedge A) and1_out == (not1_out & C)
    );
    // or0 implements and0_out | and1_out.
    check_or0_definition: assert property (
        @(posedge A) or0_out == (and0_out | and1_out)
    );
    // buf0 forwards or0_out to Y.
    check_buf0_definition: assert property (
        @(posedge A) Y == or0_out
    );

    ///// Simple implications from the Boolean function /////
    // If B is 0 then Y must be 0.
    check_b_zero_forces_y_zero: assert property (
        @(posedge A) (B == 1'b0) |-> (Y == 1'b0)
    );
    // Y high implies B is high.
    check_y_implies_b: assert property (
        @(posedge A) (Y == 1'b1) |-> (B == 1'b1)
    );
    // If B is high and (A or C) is high then Y is high.
    check_b_and_aorc_implies_y: assert property (
        @(posedge A) (B & (A | C)) |-> (Y == 1'b1)
    );
    // If both A and C are low then Y is low.
    check_a0_c0_forces_y0: assert property (
        @(posedge A) ((A == 1'b0) && (C == 1'b0)) |-> (Y == 1'b0)
    );
endmodule