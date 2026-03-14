module sky130_fd_sc_ms__and2b_sva (
    input logic clk,
    input logic X,
    input logic A_N,
    input logic B
);
    // X implements (~A_N) & B
    check_functional_equivalence: assert property (
        @(posedge clk) X == ((~A_N) & B)
    );

    // If A_N is HIGH, X must be LOW
    check_zero_when_A_N_high: assert property (
        @(posedge clk) A_N |-> (X == 1'b0)
    );

    // If B is LOW, X must be LOW
    check_zero_when_B_low: assert property (
        @(posedge clk) !B |-> (X == 1'b0)
    );

    // If A_N is LOW and B is HIGH, X must be HIGH
    check_one_when_A_N_low_and_B_high: assert property (
        @(posedge clk) (!A_N && B) |-> (X == 1'b1)
    );

    // If X is HIGH, then A_N must be LOW and B must be HIGH
    check_inputs_when_X_high: assert property (
        @(posedge clk) X |-> (!A_N && B)
    );

    // If X is LOW while B is HIGH, then A_N must be HIGH
    check_A_N_high_when_X_low_and_B_high: assert property (
        @(posedge clk) ((X == 1'b0) && B) |-> A_N
    );

    // If X is LOW while A_N is LOW, then B must be LOW
    check_B_low_when_X_low_and_A_N_low: assert property (
        @(posedge clk) ((X == 1'b0) && !A_N) |-> !B
    );
endmodule