module my_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // Y matches the implemented NAND-AND-NOT function.
    check_y_function: assert property (
        @(posedge clk) Y == ~((~(A2 & A1)) & (~(B2 & B1)))
    );

    // If both A inputs are high, Y must be low.
    check_y_low_when_a_pair_high: assert property (
        @(posedge clk) (A1 & A2) |-> !Y
    );

    // If both B inputs are high, Y must be low.
    check_y_low_when_b_pair_high: assert property (
        @(posedge clk) (B1 & B2) |-> !Y
    );

    // If neither input pair is high, Y must be high.
    check_y_high_when_no_pair_high: assert property (
        @(posedge clk) (!(A1 & A2) && !(B1 & B2)) |-> Y
    );

    // A high Y means at least one input pair is high.
    check_y_high_implies_some_pair_high: assert property (
        @(posedge clk) Y |-> ((A1 & A2) || (B1 & B2))
    );

    // A low Y means both input pairs are not high.
    check_y_low_implies_no_pair_high: assert property (
        @(posedge clk) !Y |-> (!(A1 & A2) && !(B1 & B2))
    );

endmodule