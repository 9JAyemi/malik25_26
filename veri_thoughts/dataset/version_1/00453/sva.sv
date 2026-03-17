module test_sva (
    input logic a1,
    input logic s1,
    input logic s2,
    input logic s3,
    input logic i1,
    input logic i2,
    input logic i3,
    input logic i4,
    input logic i5,
    input logic i6,
    input logic i7,
    input logic i8
);

    // i1 is the AND of a1 and s1.
    check_i1_definition: assert property (
        @($global_clock) i1 == (a1 & s1)
    );

    // i2 is the AND of a1 and s2.
    check_i2_definition: assert property (
        @($global_clock) i2 == (a1 & s2)
    );

    // i3 is the AND of a1 and s3.
    check_i3_definition: assert property (
        @($global_clock) i3 == (a1 & s3)
    );

    // i4 is the AND of not-a1 and s1.
    check_i4_definition: assert property (
        @($global_clock) i4 == ((~a1) & s1)
    );

    // i5 is the AND of not-a1 and s2.
    check_i5_definition: assert property (
        @($global_clock) i5 == ((~a1) & s2)
    );

    // i6 is the AND of not-a1 and s3.
    check_i6_definition: assert property (
        @($global_clock) i6 == ((~a1) & s3)
    );

    // i7 is high only when s1, s2, and s3 are all high.
    check_i7_definition: assert property (
        @($global_clock) i7 == (s1 & s2 & s3)
    );

    // i8 is high only when a1, s1, s2, and s3 are all low.
    check_i8_definition: assert property (
        @($global_clock) i8 == ((~a1) & (~s1) & (~s2) & (~s3))
    );

    // s1 is represented by exactly one of i1 or i4 when asserted.
    check_s1_partition: assert property (
        @($global_clock) (((i1 | i4) == s1) && !(i1 & i4))
    );

    // s2 is represented by exactly one of i2 or i5 when asserted.
    check_s2_partition: assert property (
        @($global_clock) (((i2 | i5) == s2) && !(i2 & i5))
    );

    // s3 is represented by exactly one of i3 or i6 when asserted.
    check_s3_partition: assert property (
        @($global_clock) (((i3 | i6) == s3) && !(i3 & i6))
    );

endmodule