module select_logic_sva (
    input logic i1,
    input logic i2,
    input logic i3,
    input logic i4,
    input logic i5,
    input logic i6,
    input logic i7,
    input logic i8,
    input logic s1,
    input logic s2,
    input logic s3,
    input logic a1
);

    // a1 must match the RTL mux equation.
    check_mux_equation: assert property (
        @($global_clock)
        a1 == ((i1 & (!s1) & (!s2) & (!s3)) |
               (i2 & (!s1) & (!s2) & ( s3)) |
               (i3 & (!s1) & ( s2) & (!s3)) |
               (i4 & (!s1) & ( s2) & ( s3)) |
               (i5 & ( s1) & (!s2) & (!s3)) |
               (i6 & ( s1) & (!s2) & ( s3)) |
               (i7 & ( s1) & ( s2) & (!s3)) |
               (i8 & ( s1) & ( s2) & ( s3)))
    );

    // When select is 000, a1 must equal i1.
    check_select_000_i1: assert property (
        @($global_clock)
        ({s1, s2, s3} == 3'b000) |-> (a1 == i1)
    );

    // When select is 001, a1 must equal i2.
    check_select_001_i2: assert property (
        @($global_clock)
        ({s1, s2, s3} == 3'b001) |-> (a1 == i2)
    );

    // When select is 010, a1 must equal i3.
    check_select_010_i3: assert property (
        @($global_clock)
        ({s1, s2, s3} == 3'b010) |-> (a1 == i3)
    );

    // When select is 011, a1 must equal i4.
    check_select_011_i4: assert property (
        @($global_clock)
        ({s1, s2, s3} == 3'b011) |-> (a1 == i4)
    );

    // When select is 100, a1 must equal i5.
    check_select_100_i5: assert property (
        @($global_clock)
        ({s1, s2, s3} == 3'b100) |-> (a1 == i5)
    );

    // When select is 101, a1 must equal i6.
    check_select_101_i6: assert property (
        @($global_clock)
        ({s1, s2, s3} == 3'b101) |-> (a1 == i6)
    );

    // When select is 110, a1 must equal i7.
    check_select_110_i7: assert property (
        @($global_clock)
        ({s1, s2, s3} == 3'b110) |-> (a1 == i7)
    );

    // When select is 111, a1 must equal i8.
    check_select_111_i8: assert property (
        @($global_clock)
        ({s1, s2, s3} == 3'b111) |-> (a1 == i8)
    );

endmodule