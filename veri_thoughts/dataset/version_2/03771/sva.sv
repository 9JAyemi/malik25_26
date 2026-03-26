module nand4_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Y must equal the NAND of all four inputs.
    check_nand_function: assert property (
        @(posedge clk) Y == ~(A & B & C & D)
    );

    // When all inputs are HIGH, Y must be LOW.
    check_all_inputs_high_drive_y_low: assert property (
        @(posedge clk) (A & B & C & D) |-> !Y
    );

    // If the inputs are not all HIGH, Y must be HIGH.
    check_not_all_inputs_high_drive_y_high: assert property (
        @(posedge clk) (~(A & B & C & D)) |-> Y
    );

    // Y LOW can only occur when all inputs are HIGH.
    check_y_low_implies_all_inputs_high: assert property (
        @(posedge clk) !Y |-> (A & B & C & D)
    );

    // Y HIGH means the inputs are not all HIGH.
    check_y_high_implies_not_all_inputs_high: assert property (
        @(posedge clk) Y |-> ~(A & B & C & D)
    );

endmodule