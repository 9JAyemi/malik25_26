module sky130_fd_sc_hd__a31o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);
    // X equals (A1 & A2 & A3) | B1 sampled on A1 rising.
    check_func_on_A1: assert property (
        @(posedge A1) X == ((A1 & A2 & A3) | B1)
    );

    // X equals (A1 & A2 & A3) | B1 sampled on A2 rising.
    check_func_on_A2: assert property (
        @(posedge A2) X == ((A1 & A2 & A3) | B1)
    );

    // X equals (A1 & A2 & A3) | B1 sampled on A3 rising.
    check_func_on_A3: assert property (
        @(posedge A3) X == ((A1 & A2 & A3) | B1)
    );

    // X equals (A1 & A2 & A3) | B1 sampled on B1 rising.
    check_func_on_B1: assert property (
        @(posedge B1) X == ((A1 & A2 & A3) | B1)
    );

    // X equals (A1 & A2 & A3) | B1 sampled on X rising.
    check_func_on_X: assert property (
        @(posedge X) X == ((A1 & A2 & A3) | B1)
    );

    // B1 rising forces X HIGH due to OR term.
    check_B1_rise_forces_X1: assert property (
        @(posedge B1) X == 1'b1
    );

    // When B1 is LOW, X equals A1&A2&A3 (sampled on A1 rising).
    check_B1_low_and_path_on_A1: assert property (
        @(posedge A1) (B1 == 1'b0) |-> (X == (A1 & A2 & A3))
    );

    // When B1 is LOW, X equals A1&A2&A3 (sampled on A2 rising).
    check_B1_low_and_path_on_A2: assert property (
        @(posedge A2) (B1 == 1'b0) |-> (X == (A1 & A2 & A3))
    );

    // When B1 is LOW, X equals A1&A2&A3 (sampled on A3 rising).
    check_B1_low_and_path_on_A3: assert property (
        @(posedge A3) (B1 == 1'b0) |-> (X == (A1 & A2 & A3))
    );

    // If X is LOW on A1 rising, then B1 must be LOW and at least one of A2/A3 is LOW.
    check_X0_implies_B10_and_some_A_low_on_A1: assert property (
        @(posedge A1) (X == 1'b0) |-> ((B1 == 1'b0) && ((A2 == 1'b0) || (A3 == 1'b0)))
    );
endmodule