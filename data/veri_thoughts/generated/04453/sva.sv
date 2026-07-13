module and_gate_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C
);

    // Y must implement A & B & ~C.
    check_y_function: assert property (
        @(posedge clk) Y === (A & B & ~C)
    );

    // When A, B, and ~C are true, Y must be high.
    check_y_high_when_inputs_match: assert property (
        @(posedge clk) (A & B & ~C) |-> (Y === 1'b1)
    );

    // A low forces Y low.
    check_a_low_forces_y_low: assert property (
        @(posedge clk) (A === 1'b0) |-> (Y === 1'b0)
    );

    // B low forces Y low.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) (B === 1'b0) |-> (Y === 1'b0)
    );

    // C high forces Y low.
    check_c_high_forces_y_low: assert property (
        @(posedge clk) (C === 1'b1) |-> (Y === 1'b0)
    );

    // Y high implies A and B are high and C is low.
    check_y_high_implies_inputs_match: assert property (
        @(posedge clk) (Y === 1'b1) |-> ((A === 1'b1) && (B === 1'b1) && (C === 1'b0))
    );

    // Stable inputs must produce a stable sampled output.
    check_stable_inputs_keep_y_stable: assert property (
        @(posedge clk) $stable({A, B, C}) |-> $stable(Y)
    );

endmodule