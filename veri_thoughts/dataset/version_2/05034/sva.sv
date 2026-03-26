module NAND2_CLR_assertions (
    input logic clk,
    input logic A,
    input logic B,
    input logic CLR,
    input logic Y,
    input logic Yn
);

    // Clear drives Y low.
    check_clear_forces_y_low: assert property (
        @(posedge clk) CLR |-> (Y == 1'b0)
    );

    // Clear drives Yn high.
    check_clear_forces_yn_high: assert property (
        @(posedge clk) CLR |-> (Yn == 1'b1)
    );

    // Without clear, Y is the NAND of A and B.
    check_y_matches_nand_when_not_cleared: assert property (
        @(posedge clk) disable iff (CLR) (Y == ~(A & B))
    );

    // Without clear, Yn is the AND of A and B.
    check_yn_matches_and_when_not_cleared: assert property (
        @(posedge clk) disable iff (CLR) (Yn == (A & B))
    );

    // The outputs are always complementary.
    check_outputs_are_complementary: assert property (
        @(posedge clk) (Y == ~Yn)
    );

endmodule