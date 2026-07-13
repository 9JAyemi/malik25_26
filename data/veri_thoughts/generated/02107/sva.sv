module sky130_fd_sc_hd__a21bo_sva (
    input  logic clk,   // sampling clock for assertions (DUT has no clock)
    input  logic X,
    input  logic A1,
    input  logic A2,
    input  logic B1_N
);
    // DUT is purely combinational; no reset. Function: X = (~B1_N) | (A1 & A2).

    // X must equal (~B1_N) | (A1 & A2).
    check_function_equivalence: assert property (
        @(posedge clk) X == ((~B1_N) | (A1 & A2))
    );

    // When B1_N is LOW, X must be HIGH.
    check_X_high_when_B1N_low: assert property (
        @(posedge clk) (B1_N == 1'b0) |-> (X == 1'b1)
    );

    // When A1 and A2 are HIGH, X must be HIGH (independent of B1_N).
    check_X_high_when_A1A2_high: assert property (
        @(posedge clk) (A1 && A2) |-> (X == 1'b1)
    );

    // If B1_N is HIGH and A1 is LOW, X must be LOW.
    check_X_low_when_B1N_high_A1_low: assert property (
        @(posedge clk) (B1_N && !A1) |-> (X == 1'b0)
    );

    // If B1_N is HIGH and A2 is LOW, X must be LOW.
    check_X_low_when_B1N_high_A2_low: assert property (
        @(posedge clk) (B1_N && !A2) |-> (X == 1'b0)
    );

    // If X is LOW, then B1_N is HIGH and not (A1 & A2).
    check_zero_implies_conditions: assert property (
        @(posedge clk) (X == 1'b0) |-> (B1_N && !(A1 && A2))
    );

    // If X is HIGH, then B1_N is LOW or (A1 & A2) is HIGH.
    check_one_implies_conditions: assert property (
        @(posedge clk) (X == 1'b1) |-> ((~B1_N) || (A1 && A2))
    );

    // When B1_N is HIGH, X must equal (A1 & A2).
    check_X_equals_A1A2_when_B1N_high: assert property (
        @(posedge clk) (B1_N == 1'b1) |-> (X == (A1 & A2))
    );

endmodule