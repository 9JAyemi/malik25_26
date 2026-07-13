module NAND4AND2_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic [1:0] Z
);

    // Z[0] is always high because the final NAND has two identical inputs.
    check_z0_high: assert property (
        @(posedge clk) Z[0] == 1'b1
    );

    // Z[1] is the inverted AND of A and B.
    check_z1_is_ab_and_inverted: assert property (
        @(posedge clk) Z[1] == ~(A & B)
    );

    // If A and B are both high, Z[1] must be low.
    check_z1_low_when_ab_high: assert property (
        @(posedge clk) (A & B) |-> (Z[1] == 1'b0)
    );

    // If A and B are not both high, Z[1] must be high.
    check_z1_high_when_ab_not_both_high: assert property (
        @(posedge clk) !(A & B) |-> (Z[1] == 1'b1)
    );

    // If A is low, Z[1] must be high.
    check_z1_high_when_a_low: assert property (
        @(posedge clk) !A |-> (Z[1] == 1'b1)
    );

    // If B is low, Z[1] must be high.
    check_z1_high_when_b_low: assert property (
        @(posedge clk) !B |-> (Z[1] == 1'b1)
    );

    // If A and B are both low, Z[1] must be high.
    check_z1_high_when_ab_low: assert property (
        @(posedge clk) !(A | B) |-> (Z[1] == 1'b1)
    );

endmodule