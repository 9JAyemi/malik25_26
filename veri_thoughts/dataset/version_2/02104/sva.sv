module sky130_fd_sc_hdll__o21a_sva (
    input  logic CLK,  // sampling clock for assertions
    input  logic X,
    input  logic A1,
    input  logic A2,
    input  logic B1
);
    // Combinational DUT: no clock/reset; X = (A1 | A2) & B1.

    // X equals (A1 | A2) & B1.
    check_function_equivalence: assert property (
        @(posedge CLK) X == ((A1 | A2) & B1)
    );

    // B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge CLK) (B1 == 1'b0) |-> (X == 1'b0)
    );

    // When B1 is high, X equals (A1 | A2).
    check_b1_high_passes_or: assert property (
        @(posedge CLK) (B1 == 1'b1) |-> (X == (A1 | A2))
    );

    // X high implies B1 is high and at least one of A1/A2 is high.
    check_x_high_implies_inputs: assert property (
        @(posedge CLK) (X == 1'b1) |-> (B1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1))
    );

    // If both A1 and A2 are low, X must be low.
    check_both_inputs_low_implies_x_low: assert property (
        @(posedge CLK) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // If A1 and B1 are high, X must be high (independent of A2).
    check_a1_and_b1_set_x: assert property (
        @(posedge CLK) ((A1 == 1'b1) && (B1 == 1'b1)) |-> (X == 1'b1)
    );

    // If A2 and B1 are high, X must be high (independent of A1).
    check_a2_and_b1_set_x: assert property (
        @(posedge CLK) ((A2 == 1'b1) && (B1 == 1'b1)) |-> (X == 1'b1)
    );

    // If inputs are stable, output is stable (pure combinational behavior).
    check_stability_on_stable_inputs: assert property (
        @(posedge CLK) $stable({A1, A2, B1}) |-> $stable(X)
    );
endmodule