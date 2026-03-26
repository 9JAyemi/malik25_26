module full_adder_2bit_sva (
    input logic clk,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic Cin,
    input logic [1:0] S,
    input logic Cout
);

    // Sum bits are the bitwise XOR of A and B.
    check_sum_matches_xor: assert property (
        @(posedge clk) S === (A ^ B)
    );

    // Cout matches the OR of both half-adder carries and Cin.
    check_cout_matches_or_of_carries_and_cin: assert property (
        @(posedge clk) Cout === ((A[0] & B[0]) | (A[1] & B[1]) | Cin)
    );

    // Changing only Cin must not change the sum outputs.
    check_cin_does_not_affect_sum: assert property (
        @(posedge clk) $changed(Cin) && $stable(A) && $stable(B) |-> $stable(S)
    );

    // Lower sum bit depends only on A[0] and B[0].
    check_lower_sum_isolated: assert property (
        @(posedge clk) $stable(A[0]) && $stable(B[0]) |-> $stable(S[0])
    );

    // Upper sum bit depends only on A[1] and B[1].
    check_upper_sum_isolated: assert property (
        @(posedge clk) $stable(A[1]) && $stable(B[1]) |-> $stable(S[1])
    );

    // A carry generated on bit 0 must drive Cout high.
    check_lower_carry_forces_cout: assert property (
        @(posedge clk) (A[0] & B[0]) |-> Cout
    );

    // A carry generated on bit 1 must drive Cout high.
    check_upper_carry_forces_cout: assert property (
        @(posedge clk) (A[1] & B[1]) |-> Cout
    );

    // With no carry sources active, Cout must be low.
    check_no_carry_sources_clear_cout: assert property (
        @(posedge clk) (!Cin && !(A[0] & B[0]) && !(A[1] & B[1])) |-> !Cout
    );

endmodule