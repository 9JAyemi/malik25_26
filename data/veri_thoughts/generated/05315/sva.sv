module sky130_fd_sc_hdll__o22ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // Output matches the implemented OR-of-NORs function.
    check_o22ai_function: assert property (
        @(posedge clk) Y == ((~(A1 | A2)) | (~(B1 | B2)))
    );

    // If both A inputs are low, the output must be high.
    check_a_pair_low_forces_high: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // If both B inputs are low, the output must be high.
    check_b_pair_low_forces_high: assert property (
        @(posedge clk) ((B1 == 1'b0) && (B2 == 1'b0)) |-> (Y == 1'b1)
    );

    // If either A input and either B input are high, the output must be low.
    check_both_sides_active_force_low: assert property (
        @(posedge clk) (((A1 == 1'b1) || (A2 == 1'b1)) && ((B1 == 1'b1) || (B2 == 1'b1))) |-> (Y == 1'b0)
    );

    // All-low inputs produce a high output.
    check_all_inputs_low: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0) && (B1 == 1'b0) && (B2 == 1'b0)) |-> (Y == 1'b1)
    );

    // All-high inputs produce a low output.
    check_all_inputs_high: assert property (
        @(posedge clk) ((A1 == 1'b1) && (A2 == 1'b1) && (B1 == 1'b1) && (B2 == 1'b1)) |-> (Y == 1'b0)
    );

    // When the A-side NOR is low, the output depends only on the B-side NOR.
    check_a_pair_high_reduces_to_b_nor: assert property (
        @(posedge clk) ((A1 == 1'b1) && (A2 == 1'b1)) |-> (Y == (~(B1 | B2)))
    );

    // When the B-side NOR is low, the output depends only on the A-side NOR.
    check_b_pair_high_reduces_to_a_nor: assert property (
        @(posedge clk) ((B1 == 1'b1) && (B2 == 1'b1)) |-> (Y == (~(A1 | A2)))
    );

endmodule