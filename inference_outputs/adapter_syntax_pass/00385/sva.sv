module my_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // Y matches the implemented NAND/AND/NOT/buffer function.
    check_y_matches_function: assert property (
        @(posedge clk) Y == ~((~(A2 & A1)) & (~(B2 & B1)))
    );

    // A low A1 forces Y high.
    check_a1_low_forces_y_high: assert property (
        @(posedge clk) (A1 == 1'b0) |-> (Y == 1'b1)
    );

    // A low A2 forces Y high.
    check_a2_low_forces_y_high: assert property (
        @(posedge clk) (A2 == 1'b0) |-> (Y == 1'b1)
    );

    // A low B1 forces Y high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // A low B2 forces Y high.
    check_b2_low_forces_y_high: assert property (
        @(posedge clk) (B2 == 1'b0) |-> (Y == 1'b1)
    );

    // A1 and A2 high with B1 and B2 high force Y low.
    check_all_high_inputs_force_y_low: assert property (
        @(posedge clk) ((A1 == 1'b1) && (A2 == 1'b1) && (B1 == 1'b1) && (B2 == 1'b1)) |-> (Y == 1'b0)
    );

    // A low Y requires both A inputs and both B inputs to be high.
    check_y_low_requires_all_high_inputs: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((A1 == 1'b1) && (A2 == 1'b1) && (B1 == 1'b1) && (B2 == 1'b1))
    );

endmodule