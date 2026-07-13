module bitwise_and_sva (
    input logic        clk,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [31:0] Q
);

    // Q captures the previous cycle's bitwise AND of A and B.
    check_q_updates_to_prev_and: assert property (
        @(posedge clk) 1'b1 |=> (Q == ($past(A) & $past(B)))
    );

    // If A and B have no overlapping 1 bits, Q becomes zero on the next cycle.
    check_zero_when_no_bit_overlap: assert property (
        @(posedge clk) ((A & B) == 32'h0000_0000) |=> (Q == 32'h0000_0000)
    );

    // If A is all ones, Q captures the previous value of B.
    check_q_matches_prev_b_when_a_all_ones: assert property (
        @(posedge clk) (A == 32'hFFFF_FFFF) |=> (Q == $past(B))
    );

    // If B is all ones, Q captures the previous value of A.
    check_q_matches_prev_a_when_b_all_ones: assert property (
        @(posedge clk) (B == 32'hFFFF_FFFF) |=> (Q == $past(A))
    );

    // Q cannot contain 1 bits that were not set in the previous A value.
    check_q_subset_of_prev_a: assert property (
        @(posedge clk) 1'b1 |=> ((Q & ~$past(A)) == 32'h0000_0000)
    );

    // Q cannot contain 1 bits that were not set in the previous B value.
    check_q_subset_of_prev_b: assert property (
        @(posedge clk) 1'b1 |=> ((Q & ~$past(B)) == 32'h0000_0000)
    );

endmodule