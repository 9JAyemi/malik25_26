module magnitude_comparator_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       out
);
    // No clock/reset in DUT; combinational; sample on edges of A/B/out.

    // Core relation: out equals (|A) & ~(|B) on A[0] edges.
    check_func_equiv_on_A0: assert property (
        @(posedge A[0]) out == ((|A) & ~(|B))
    );

    // If A is zero, out must be 0.
    check_out_zero_when_A_zero_on_A1: assert property (
        @(posedge A[1]) (A == 4'd0) |-> (out == 1'b0)
    );

    // If B is nonzero, out must be 0.
    check_out_zero_when_B_nonzero_on_B0: assert property (
        @(posedge B[0]) (B != 4'd0) |-> (out == 1'b0)
    );

    // If A is nonzero and B is zero, out must be 1.
    check_out_one_when_Ane0_Beq0_on_A2: assert property (
        @(posedge A[2]) ((A != 4'd0) && (B == 4'd0)) |-> (out == 1'b1)
    );

    // If out is 1, A must be nonzero and B must be zero.
    check_out_one_only_if_Ane0_Beq0_on_A3: assert property (
        @(posedge A[3]) (out == 1'b1) |-> ((A != 4'd0) && (B == 4'd0))
    );

    // If both A and B are zero, out must be 0.
    check_out_zero_when_both_zero_on_B1: assert property (
        @(posedge B[1]) ((A == 4'd0) && (B == 4'd0)) |-> (out == 1'b0)
    );

    // If both A and B are nonzero, out must be 0.
    check_out_zero_when_both_nonzero_on_B2: assert property (
        @(posedge B[2]) ((A != 4'd0) && (B != 4'd0)) |-> (out == 1'b0)
    );

    // If out is 0, then either A is zero or B is nonzero.
    check_out_zero_implies_Azero_or_Bnonzero_on_B3: assert property (
        @(posedge B[3]) (out == 1'b0) |-> ((A == 4'd0) || (B != 4'd0))
    );

    // When out rises, A must be nonzero and B must be zero.
    check_out_rise_requires_Ane0_Beq0_on_out: assert property (
        @(posedge out) ((A != 4'd0) && (B == 4'd0))
    );

    // When A is nonzero, out equals ~(|B).
    check_when_A_nonzero_out_eq_not_reduceB_on_A0: assert property (
        @(posedge A[0]) (A != 4'd0) |-> (out == ~(|B))
    );

endmodule