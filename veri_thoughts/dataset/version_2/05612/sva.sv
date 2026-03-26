module nand4bb_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D
);

    // Y implements (A_N & B_N) | (C & D).
    check_y_matches_boolean_function: assert property (
        @(posedge clk) Y == ((A_N & B_N) | (C & D))
    );

    // A_N and B_N both high force Y high.
    check_y_high_when_ab_high: assert property (
        @(posedge clk) (A_N & B_N) |-> (Y == 1'b1)
    );

    // C and D both high force Y high.
    check_y_high_when_cd_high: assert property (
        @(posedge clk) (C & D) |-> (Y == 1'b1)
    );

    // If neither input pair is high, Y must be low.
    check_y_low_when_no_pair_high: assert property (
        @(posedge clk) !((A_N & B_N) | (C & D)) |-> (Y == 1'b0)
    );

    // A high Y requires at least one high input pair.
    check_y_high_requires_ab_or_cd: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((A_N & B_N) | (C & D))
    );

endmodule