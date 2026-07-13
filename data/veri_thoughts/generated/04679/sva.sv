module AND4_assertions (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Z
);

    // Z must equal the AND of all four inputs.
    check_z_matches_four_input_and: assert property (
        @(posedge clk) Z == (A & B & C & D)
    );

    // If all inputs are high, Z must be high.
    check_all_high_implies_z_high: assert property (
        @(posedge clk) (A & B & C & D) |-> Z
    );

    // If any input is low, Z must be low.
    check_any_low_implies_z_low: assert property (
        @(posedge clk) (!A || !B || !C || !D) |-> !Z
    );

    // Z can only be high when all inputs are high.
    check_z_high_requires_all_high: assert property (
        @(posedge clk) Z |-> (A & B & C & D)
    );

endmodule