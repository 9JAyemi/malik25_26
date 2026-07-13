module sky130_fd_sc_lp__a21o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1
);

    // X implements the boolean function (A1 & A2) | B1.
    check_output_function: assert property (
        @(posedge clk) X == ((A1 & A2) | B1)
    );

    // B1 high must force X high.
    check_b1_forces_high: assert property (
        @(posedge clk) B1 |-> X
    );

    // With B1 low, X must equal the AND of A1 and A2.
    check_and_path_when_b1_low: assert property (
        @(posedge clk) !B1 |-> (X == (A1 & A2))
    );

    // If A1 is low while B1 is low, X must be low.
    check_a1_low_blocks_output_without_b1: assert property (
        @(posedge clk) (!B1 && !A1) |-> !X
    );

    // If A2 is low while B1 is low, X must be low.
    check_a2_low_blocks_output_without_b1: assert property (
        @(posedge clk) (!B1 && !A2) |-> !X
    );

    // When both A inputs are high, X must be high.
    check_a_inputs_high_drive_output: assert property (
        @(posedge clk) (A1 && A2) |-> X
    );

endmodule