module and4_4_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Combinational 4-input AND; clk is only used to sample the RTL and there is no reset.

    // X must match the AND of all four inputs.
    check_output_matches_and4: assert property (
        @(posedge clk) X == (A & B & C & D)
    );

    // Any low input forces X low.
    check_any_low_forces_x_low: assert property (
        @(posedge clk) ((!A) || (!B) || (!C) || (!D)) |-> (!X)
    );

    // All inputs high drive X high.
    check_all_high_drives_x_high: assert property (
        @(posedge clk) (A && B && C && D) |-> X
    );

    // A high X requires every input to be high.
    check_x_high_requires_all_high: assert property (
        @(posedge clk) X |-> (A && B && C && D)
    );

endmodule