module multiplier_2x2_sva (
    input logic clk,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic [3:0] P,
    input logic [3:0] Q
);

    // P is A gated by B[0], zero-extended to 4 bits.
    check_p_matches_b0_product: assert property (
        @(posedge clk) P == {2'b00, (A & {2{B[0]}})}
    );

    // Q is A gated by B[1], zero-extended to 4 bits.
    check_q_matches_b1_product: assert property (
        @(posedge clk) Q == {2'b00, (A & {2{B[1]}})}
    );

    // P stays unchanged when A and B[0] stay unchanged.
    check_p_stable_when_a_and_b0_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B[0])) |-> $stable(P)
    );

    // Q stays unchanged when A and B[1] stay unchanged.
    check_q_stable_when_a_and_b1_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B[1])) |-> $stable(Q)
    );

endmodule