module sky130_fd_sc_ls__a32oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);

    // Y matches the implemented NAND/AND/buffer function.
    check_y_matches_function: assert property (
        @(posedge clk) Y == ((~(A2 & A1 & A3)) & (~(B2 & B1)))
    );

    // All three A inputs high force Y low.
    check_a_triplet_forces_low: assert property (
        @(posedge clk) (A1 & A2 & A3) |-> !Y
    );

    // All two B inputs high force Y low.
    check_b_pair_forces_low: assert property (
        @(posedge clk) (B1 & B2) |-> !Y
    );

    // With no A-side high triplet and no B-side high pair, Y is high.
    check_no_active_inputs_drive_high: assert property (
        @(posedge clk) (!(A1 & A2 & A3) && !(B1 & B2)) |-> Y
    );

    // A low Y must come from the A-side triplet or the B-side pair.
    check_low_output_has_cause: assert property (
        @(posedge clk) !Y |-> ((A1 & A2 & A3) || (B1 & B2))
    );

    // A high Y means the A-side triplet is not active and the B-side pair is not active.
    check_high_output_means_no_active_inputs: assert property (
        @(posedge clk) Y |-> (!(A1 & A2 & A3) && !(B1 & B2))
    );

endmodule