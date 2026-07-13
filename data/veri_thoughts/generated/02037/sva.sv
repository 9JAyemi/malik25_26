module comparator_2bit_sva (
    input logic [1:0] A,
    input logic [1:0] B,
    input logic       EQ
);
    // No explicit clock/reset in RTL; sample on any input/output edge.
    localparam dummy = 1'b0;

    // EQ must be 1 when A equals B (4-state equality).
    check_eq_when_equal: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1]
        or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1]
        or posedge EQ or negedge EQ)
        (A == B) |-> (EQ == 1'b1)
    );

    // EQ must be 0 when A does not equal B (4-state inequality is true).
    check_eq_low_when_unequal: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1]
        or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1]
        or posedge EQ or negedge EQ)
        (A != B) |-> (EQ == 1'b0)
    );

    // If EQ is 1, inputs must be equal.
    check_eq_one_implies_equal: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1]
        or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1]
        or posedge EQ or negedge EQ)
        (EQ == 1'b1) |-> (A == B)
    );

    // Output is binary 0/1 (never X/Z at sampling times).
    check_output_is_binary: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1]
        or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1]
        or posedge EQ or negedge EQ)
        (EQ inside {1'b0, 1'b1})
    );

    // If inputs are stable, output must be stable (pure combinational behavior).
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1]
        or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1]
        or posedge EQ or negedge EQ)
        ($stable(A) && $stable(B)) |-> $stable(EQ)
    );

    // Output changes only if at least one input changed.
    check_output_change_requires_input_change: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1]
        or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1]
        or posedge EQ or negedge EQ)
        $changed(EQ) |-> (!$stable(A) || !$stable(B))
    );
endmodule