module two_bit_adder_sva (
    input logic X,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    input logic OUT
);
    // OUT equals logical AND of A1_N, A2_N, B1, and B2.
    check_functional_equivalence: assert property (
        @(posedge X) OUT == (A1_N && A2_N && B1 && B2)
    );

    // If all inputs are HIGH, OUT must be HIGH.
    check_all_high_implies_out_high: assert property (
        @(posedge X) (A1_N && A2_N && B1 && B2) |-> (OUT == 1'b1)
    );

    // OUT HIGH requires A1_N HIGH.
    check_out_requires_A1_N: assert property (
        @(posedge X) OUT |-> A1_N
    );

    // OUT HIGH requires A2_N HIGH.
    check_out_requires_A2_N: assert property (
        @(posedge X) OUT |-> A2_N
    );

    // OUT HIGH requires B1 HIGH.
    check_out_requires_B1: assert property (
        @(posedge X) OUT |-> B1
    );

    // OUT HIGH requires B2 HIGH.
    check_out_requires_B2: assert property (
        @(posedge X) OUT |-> B2
    );

    // A1_N LOW forces OUT LOW.
    check_a1n_low_forces_out_low: assert property (
        @(posedge X) (!A1_N) |-> (OUT == 1'b0)
    );

    // A2_N LOW forces OUT LOW.
    check_a2n_low_forces_out_low: assert property (
        @(posedge X) (!A2_N) |-> (OUT == 1'b0)
    );

    // B1 LOW forces OUT LOW.
    check_b1_low_forces_out_low: assert property (
        @(posedge X) (!B1) |-> (OUT == 1'b0)
    );

    // B2 LOW forces OUT LOW.
    check_b2_low_forces_out_low: assert property (
        @(posedge X) (!B2) |-> (OUT == 1'b0)
    );

    // If A1_N, A2_N, B1, B2 are stable cycle-to-cycle, OUT remains stable.
    check_stability_with_stable_inputs: assert property (
        @(posedge X) $stable({A1_N, A2_N, B1, B2}) |-> $stable(OUT)
    );
endmodule