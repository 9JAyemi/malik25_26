module half_adder_sva (
    input logic A,
    input logic B,
    input logic SUM,
    input logic COUT
);

    // SUM implements XOR of the inputs.
    check_sum_matches_xor: assert property (
        @($global_clock) SUM == (A ^ B)
    );

    // COUT implements AND of the inputs.
    check_cout_matches_and: assert property (
        @($global_clock) COUT == (A & B)
    );

    // Inputs 00 produce SUM=0 and COUT=0.
    check_00_case: assert property (
        @($global_clock) (!A && !B) |-> (!SUM && !COUT)
    );

    // Inputs 01 produce SUM=1 and COUT=0.
    check_01_case: assert property (
        @($global_clock) (!A && B) |-> (SUM && !COUT)
    );

    // Inputs 10 produce SUM=1 and COUT=0.
    check_10_case: assert property (
        @($global_clock) (A && !B) |-> (SUM && !COUT)
    );

    // Inputs 11 produce SUM=0 and COUT=1.
    check_11_case: assert property (
        @($global_clock) (A && B) |-> (!SUM && COUT)
    );

endmodule