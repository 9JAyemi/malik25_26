module and5_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1,
    input logic X
);
    // Output equals the AND of all five inputs.
    check_output_equals_and_all: assert property (
        @(posedge clk) X == (A1 & A2 & A3 & A4 & B1)
    );

    // If A1 is LOW, X must be LOW.
    check_a1_low_forces_x_low: assert property (
        @(posedge clk) (A1 == 1'b0) |-> (X == 1'b0)
    );

    // If A2 is LOW, X must be LOW.
    check_a2_low_forces_x_low: assert property (
        @(posedge clk) (A2 == 1'b0) |-> (X == 1'b0)
    );

    // If A3 is LOW, X must be LOW.
    check_a3_low_forces_x_low: assert property (
        @(posedge clk) (A3 == 1'b0) |-> (X == 1'b0)
    );

    // If A4 is LOW, X must be LOW.
    check_a4_low_forces_x_low: assert property (
        @(posedge clk) (A4 == 1'b0) |-> (X == 1'b0)
    );

    // If B1 is LOW, X must be LOW.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) (B1 == 1'b0) |-> (X == 1'b0)
    );

    // If all inputs are HIGH, X must be HIGH.
    check_all_high_drives_x_high: assert property (
        @(posedge clk) (A1 & A2 & A3 & A4 & B1) |-> (X == 1'b1)
    );

    // X can be HIGH only if all inputs are HIGH.
    check_x_high_implies_all_high: assert property (
        @(posedge clk) (X == 1'b1) |-> (A1 & A2 & A3 & A4 & B1)
    );

    // X can only rise when all inputs are HIGH.
    check_x_rise_requires_all_high: assert property (
        @(posedge clk) $rose(X) |-> (A1 & A2 & A3 & A4 & B1)
    );

    // X can only fall when at least one input is LOW.
    check_x_fall_requires_some_low: assert property (
        @(posedge clk) $fell(X) |-> (!A1 || !A2 || !A3 || !A4 || !B1)
    );
endmodule