module sky130_fd_sc_hd__and3b_sva (
    input logic clk,
    input logic X,
    input logic A_N,
    input logic B,
    input logic C
);

    // No reset in RTL; combinational behavior is sampled on clk.
    
    // X must equal the AND of B, C, and the inversion of A_N.
    check_and3b_function: assert property (
        @(posedge clk) X == ((~A_N) & B & C)
    );

    // A_N high forces the inverted input low, so X must be low.
    check_a_n_high_blocks_output: assert property (
        @(posedge clk) A_N |-> !X
    );

    // B low forces the AND output low.
    check_b_low_blocks_output: assert property (
        @(posedge clk) !B |-> !X
    );

    // C low forces the AND output low.
    check_c_low_blocks_output: assert property (
        @(posedge clk) !C |-> !X
    );

    // When A_N is low and both B and C are high, X must be high.
    check_all_enables_drive_output_high: assert property (
        @(posedge clk) (!A_N && B && C) |-> X
    );

    // X high implies A_N is low and both B and C are high.
    check_x_high_requires_all_inputs: assert property (
        @(posedge clk) X |-> (!A_N && B && C)
    );

    // With A_N low, X reduces to B AND C.
    check_a_n_low_reduces_to_bc_and: assert property (
        @(posedge clk) !A_N |-> (X == (B & C))
    );

endmodule