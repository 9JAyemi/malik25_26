module bitwise_xor_sva (
    input logic [31:0] A,
    input logic [31:0] B,
    input logic TE,
    input logic [31:0] Z
);
    // Z implements TE ? (A ^ B) : 0.
    check_functional: assert property (
        @(posedge TE or posedge A[0] or posedge B[0]) Z == (TE ? (A ^ B) : 32'h0)
    );

    // When TE is 0, Z is all zeros.
    check_zero_when_te0: assert property (
        @(posedge TE or posedge A[0] or posedge B[0]) (TE == 1'b0) |-> (Z == 32'h0)
    );

    // When TE is 1, Z equals A ^ B.
    check_xor_when_te1: assert property (
        @(posedge TE or posedge A[0] or posedge B[0]) (TE == 1'b1) |-> (Z == (A ^ B))
    );

    // If Z is non-zero, TE must be 1.
    check_nonzero_implies_te1: assert property (
        @(posedge TE or posedge A[0] or posedge B[0]) (Z != 32'h0) |-> (TE == 1'b1)
    );

    // With TE=1 and A==0, Z passes through B.
    check_passthrough_b_when_te1_a_zero: assert property (
        @(posedge TE or posedge A[0] or posedge B[0]) (TE == 1'b1 && (A == 32'h0)) |-> (Z == B)
    );

    // With TE=1 and B==0, Z passes through A.
    check_passthrough_a_when_te1_b_zero: assert property (
        @(posedge TE or posedge A[0] or posedge B[0]) (TE == 1'b1 && (B == 32'h0)) |-> (Z == A)
    );

    // With TE=1 and A==B, Z is zero.
    check_zero_when_te1_a_eq_b: assert property (
        @(posedge TE or posedge A[0] or posedge B[0]) (TE == 1'b1 && (A == B)) |-> (Z == 32'h0)
    );

    // With TE=1 and B==~A, Z is all ones.
    check_allones_when_te1_b_eq_not_a: assert property (
        @(posedge TE or posedge A[0] or posedge B[0]) (TE == 1'b1 && (B == ~A)) |-> (Z == 32'hFFFF_FFFF)
    );
endmodule