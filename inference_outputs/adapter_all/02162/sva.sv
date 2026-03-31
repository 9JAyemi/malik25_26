module sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP_B
);

    // X must match the implemented AND/NOT function.
    check_functional_equivalence: assert property (
        @(posedge clk) X == (SLEEP_B & A)
    );

    // When sleep is asserted, X must be low.
    check_sleep_forces_low: assert property (
        @(posedge clk) !SLEEP_B |-> !X
    );

    // When sleep is deasserted, X must follow A.
    check_awake_follows_a: assert property (
        @(posedge clk) SLEEP_B |-> (X == A)
    );

    // A low forces X low regardless of sleep.
    check_a_low_forces_low: assert property (
        @(posedge clk) !A |-> !X
    );

    // With sleep deasserted and A high, X must be high.
    check_awake_a_high_sets_x: assert property (
        @(posedge clk) (SLEEP_B & A) |-> X
    );

endmodule