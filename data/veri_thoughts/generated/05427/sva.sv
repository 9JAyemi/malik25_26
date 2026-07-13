module sky130_fd_sc_hdll__a21o_assertions (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1
);

    // X matches the implemented A21O logic function.
    check_functional_equivalence: assert property (
        @(posedge clk) X == ((A1 & A2) | B1)
    );

    // B1 alone is sufficient to drive X high.
    check_b1_forces_x_high: assert property (
        @(posedge clk) B1 |-> X
    );

    // The A1/A2 AND path drives X high when both inputs are high.
    check_and_path_forces_x_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // When B1 is low, X reduces to the A1/A2 AND result.
    check_b1_low_reduces_to_and: assert property (
        @(posedge clk) !B1 |-> (X == (A1 & A2))
    );

    // With B1 low and an incomplete AND path, X must be low.
    check_no_active_input_path_means_x_low: assert property (
        @(posedge clk) (!B1 && (!A1 || !A2)) |-> !X
    );

endmodule