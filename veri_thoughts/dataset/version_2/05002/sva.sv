module nand4_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);

    // Y matches the implemented NAND-tree boolean function.
    check_output_function: assert property (
        @(posedge clk) Y == ((A & B) | (C & D))
    );

    // A and B high forces Y high.
    check_ab_pair_drives_high: assert property (
        @(posedge clk) ((A & B) == 1'b1) |-> (Y == 1'b1)
    );

    // C and D high forces Y high.
    check_cd_pair_drives_high: assert property (
        @(posedge clk) ((C & D) == 1'b1) |-> (Y == 1'b1)
    );

    // With no high input pair, Y must be low.
    check_no_pair_drives_low: assert property (
        @(posedge clk) (((A & B) == 1'b0) && ((C & D) == 1'b0)) |-> (Y == 1'b0)
    );

    // A high Y requires at least one high input pair.
    check_high_output_requires_pair: assert property (
        @(posedge clk) (Y == 1'b1) |-> (((A & B) == 1'b1) || ((C & D) == 1'b1))
    );

endmodule