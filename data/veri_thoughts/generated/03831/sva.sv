module nand4b_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Y must implement ~( (A & B) | (C & D) ).
    check_output_equation: assert property (
        @(posedge clk) Y == ~((A & B) | (C & D))
    );

    // If A and B are both HIGH, Y must be LOW.
    check_ab_pair_forces_low: assert property (
        @(posedge clk) ((A & B) == 1'b1) |-> (Y == 1'b0)
    );

    // If C and D are both HIGH, Y must be LOW.
    check_cd_pair_forces_low: assert property (
        @(posedge clk) ((C & D) == 1'b1) |-> (Y == 1'b0)
    );

    // If neither pair is HIGH together, Y must be HIGH.
    check_no_pair_high_drives_high: assert property (
        @(posedge clk) (((A & B) == 1'b0) && ((C & D) == 1'b0)) |-> (Y == 1'b1)
    );

    // A LOW Y requires at least one HIGH input pair.
    check_low_output_has_active_pair: assert property (
        @(posedge clk) (Y == 1'b0) |-> (((A & B) == 1'b1) || ((C & D) == 1'b1))
    );

endmodule