module comparator_16bit_sva (
    input logic [15:0] a,
    input logic [15:0] b,
    input logic        eq
);

    // No RTL clock or reset; sample this combinational check on the formal global clock.
    // eq must exactly reflect whether the two 16-bit inputs are equal.
    check_eq_matches_comparison: assert property (
        @($global_clock) eq === (a == b)
    );

endmodule