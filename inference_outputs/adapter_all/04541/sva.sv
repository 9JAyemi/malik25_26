module twos_complement_sva (
    input logic [3:0] Y,
    input logic [3:0] A,
    input logic       invert
);
    // Y equals (A + 1) when not inverting.
    check_y_when_not_invert: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or posedge invert)
        (!invert) |-> (Y == (A + 4'd1))
    );

    // Y equals bitwise NOT of (A + 1) when inverting.
    check_y_when_invert: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or posedge invert)
        (invert) |-> (Y == ~((A + 4'd1)))
    );

    // When not inverting, Y - 1 equals A.
    check_inverse_when_not_invert: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or posedge invert)
        (!invert) |-> ((Y - 4'd1) == A)
    );

    // When inverting, Y + 1 equals bitwise NOT of A.
    check_inverse_when_invert: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or posedge invert)
        (invert) |-> ((Y + 4'd1) == ~A)
    );

    // When not inverting, Y + A equals 0 (mod 16).
    check_sum_zero_when_not_invert: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or posedge invert)
        (!invert) |-> ((Y + A) == 4'd0)
    );

    // When inverting, Y + A equals 1 (mod 16).
    check_sum_one_when_invert: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or posedge invert)
        (invert) |-> ((Y + A) == 4'd1)
    );

    // When not inverting, Y equals bitwise NOT of (A - 1).
    check_y_equals_not_a_minus1_when_not_invert: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or posedge invert)
        (!invert) |-> (Y == ~((A - 4'd1)))
    );

    // When inverting, Y equals (A - 1).
    check_y_equals_a_minus1_when_invert: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or posedge invert)
        (invert) |-> (Y == (A - 4'd1))
    );

    // When not inverting, Y equals bitwise NOT of (A + 1).
    check_y_equals_not_a_plus1_when_not_invert: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or posedge invert)
        (!invert) |-> (Y == ~((A + 4'd1)))
    );

    // When inverting, Y equals bitwise NOT of (A - 1).
    check_y_equals_not_a_minus1_when_invert: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or posedge invert)
        (invert) |-> (Y == ~((A - 4'd1)))
    );
endmodule