module bitwise_op_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] sel,
    input logic [3:0] out
);
    // Combinational DUT with no clock/reset; sample on any input edge.

    // When sel==00, out equals bitwise AND of A and B.
    check_sel00_and: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b00) |-> (out == (A & B))
    );

    // When sel==01, out equals bitwise OR of A and B.
    check_sel01_or: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b01) |-> (out == (A | B))
    );

    // When sel==10, out equals bitwise XOR of A and B.
    check_sel10_xor: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b10) |-> (out == (A ^ B))
    );

    // When sel==11, out equals bitwise NOT of XOR of A and B.
    check_sel11_notxor: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b11) |-> (out == ~(A ^ B))
    );

    // For sel==00, out equals bitwise AND of A and B.
    check_sel00_and_equiv: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b00) |-> (out == (A & B))
    );

    // For sel==01, out equals bitwise OR of A and B.
    check_sel01_or_equiv: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b01) |-> (out == (A | B))
    );

    // For sel==10, out equals bitwise XOR of A and B.
    check_sel10_xor_equiv: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b10) |-> (out == (A ^ B))
    );

    // For sel==11, out equals bitwise NOT of XOR of A and B.
    check_sel11_notxor_equiv: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b11) |-> (out == ~(A ^ B))
    );

    // For sel==00, out equals bitwise AND of A and B.
    check_sel00_and_equiv2: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b00) |-> (out == (A & B))
    );

    // For sel==01, out equals bitwise OR of A and B.
    check_sel01_or_equiv2: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b01) |-> (out == (A | B))
    );

    // For sel==10, out equals bitwise XOR of A and B.
    check_sel10_xor_equiv2: assert property (
