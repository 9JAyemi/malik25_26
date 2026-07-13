module sky130_fd_sc_ls__o21a_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1
);
    // No clock/reset in DUT; pure combinational; sample on posedge of A1/A2/B1/X.

    // X implements (A1 | A2) & B1.
    func_equivalence: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge X) X == ((A1 | A2) & B1)
    );

    // If B1 is LOW, X must be LOW.
    gate_low_when_B1_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge X) (B1 == 1'b0) |-> (X == 1'b0)
    );

    // If either A1 or A2 is HIGH and B1 is HIGH, X must be HIGH.
    drives_high_when_enabled_and_any_A: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge X) (B1 && (A1 || A2)) |-> (X == 1'b1)
    );

    // X cannot be HIGH unless B1 is HIGH.
    x_implies_b1: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge X) (X == 1'b1) |-> (B1 == 1'b1)
    );

    // X cannot be HIGH unless at least one of A1/A2 is HIGH.
    x_implies_any_a: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge X) (X == 1'b1) |-> (A1 || A2)
    );

    // If both A1 and A2 are LOW, X must be LOW.
    both_a_low_forces_x_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge X) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // If A1 and B1 are HIGH, X must be HIGH.
    a1_and_b1_implies_x_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge X) (A1 && B1) |-> (X == 1'b1)
    );

    // If A2 and B1 are HIGH, X must be HIGH.
    a2_and_b1_implies_x_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge X) (A2 && B1) |-> (X == 1'b1)
    );
endmodule