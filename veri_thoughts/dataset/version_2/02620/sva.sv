module complement_sva (
    input logic [3:0] X,
    input logic [3:0] A
);

    // On any A edge, X must equal bitwise complement of A.
    check_vector_complement: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3])
        (X == ~A)
    );

    // Bit 0: X[0] is the inverse of A[0] on any A[0] edge.
    check_x0_is_not_a0: assert property (
        @(posedge A[0] or negedge A[0]) (X[0] == ~A[0])
    );

    // Bit 1: X[1] is the inverse of A[1] on any A[1] edge.
    check_x1_is_not_a1: assert property (
        @(posedge A[1] or negedge A[1]) (X[1] == ~A[1])
    );

    // Bit 2: X[2] is the inverse of A[2] on any A[2] edge.
    check_x2_is_not_a2: assert property (
        @(posedge A[2] or negedge A[2]) (X[2] == ~A[2])
    );

    // Bit 3: X[3] is the inverse of A[3] on any A[3] edge.
    check_x3_is_not_a3: assert property (
        @(posedge A[3] or negedge A[3]) (X[3] == ~A[3])
    );

    // Any change in A must cause a change in X.
    change_in_a_changes_x: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3])
        $changed(X)
    );

    // A[0] only changes -> only X[0] changes.
    singlebit0_maps: assert property (
        @(posedge A[0] or negedge A[0])
        ($stable(A[1]) && $stable(A[2]) && $stable(A[3]))
        |-> ($changed(X[0]) && $stable(X[1]) && $stable(X[2]) && $stable(X[3]))
    );

    // A[1] only changes -> only X[1] changes.
    singlebit1_maps: assert property (
        @(posedge A[1] or negedge A[1])
        ($stable(A[0]) && $stable(A[2]) && $stable(A[3]))
        |-> ($changed(X[1]) && $stable(X[0]) && $stable(X[2]) && $stable(X[3]))
    );

    // A[2] only changes -> only X[2] changes.
    singlebit2_maps: assert property (
        @(posedge A[2] or negedge A[2])
        ($stable(A[0]) && $stable(A[1]) && $stable(A[3]))
        |-> ($changed(X[2]) && $stable(X[0]) && $stable(X[1]) && $stable(X[3]))
    );

    // A[3] only changes -> only X[3] changes.
    singlebit3_maps: assert property (
        @(posedge A[3] or negedge A[3])
        ($stable(A[0]) && $stable(A[1]) && $stable(A[2]))
        |-> ($changed(X[3]) && $stable(X[0]) && $stable(X[1]) && $stable(X[2]))
    );

    // Any change in X must correspond to a change in A.
    x_change_implies_a_change: assert property (
        @(posedge X[0] or negedge X[0] or
          posedge X[1] or negedge X[1] or
          posedge X[2] or negedge X[2] or
          posedge X[3] or negedge X[3])
        $changed(A)
    );

endmodule