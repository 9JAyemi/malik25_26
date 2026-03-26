module adder_ovf_sva (
    input logic [1:0] A,
    input logic [1:0] B,
    input logic [1:0] SUM,
    input logic OVF
);

    // No RTL clock or reset; assertions sample on the formal global clock.
    // The DUT is a combinational 2-bit unsigned adder with carry-out overflow.

    // Full 3-bit output matches zero-extended addition of A and B.
    check_full_add_result: assert property (
        @($global_clock) {OVF, SUM} == ({1'b0, A} + {1'b0, B})
    );

    // Overflow is asserted exactly when the unsigned sum is 4 or greater.
    check_overflow_threshold: assert property (
        @($global_clock) OVF == (({1'b0, A} + {1'b0, B}) >= 3'd4)
    );

    // A zero A input passes B through with no overflow.
    check_a_zero_passthrough: assert property (
        @($global_clock) (A == 2'b00) |-> (!OVF && (SUM == B))
    );

    // A zero B input passes A through with no overflow.
    check_b_zero_passthrough: assert property (
        @($global_clock) (B == 2'b00) |-> (!OVF && (SUM == A))
    );

    // The maximum input combination wraps to 2 with overflow.
    check_max_input_case: assert property (
        @($global_clock) ((A == 2'b11) && (B == 2'b11)) |-> (OVF && (SUM == 2'b10))
    );

    // Adding 2 and 2 wraps to 0 with overflow.
    check_two_plus_two_case: assert property (
        @($global_clock) ((A == 2'b10) && (B == 2'b10)) |-> (OVF && (SUM == 2'b00))
    );

endmodule