module and_gate_extra_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

// Y must equal A & B & ~C.
    check_function_equivalence: assert property (
        @(posedge clk) Y == (A & B & ~C)
    );

// When C is HIGH, Y must be LOW.
    check_c_high_forces_y_low: assert property (
        @(posedge clk) C |-> !Y
    );

// When C is LOW, Y must equal A & B.
    check_c_low_reduces_to_and: assert property (
        @(posedge clk) !C |-> (Y == (A & B))
    );

// A and B HIGH with C LOW must drive Y HIGH.
    check_all_inputs_true_drive_y_high: assert property (
        @(posedge clk) (!C && A && B) |-> Y
    );

// A LOW with C LOW must drive Y LOW.
    check_a_low_forces_y_low: assert property (
        @(posedge clk) (!C && !A) |-> !Y
    );

// B LOW with C LOW must drive Y LOW.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) (!C && !B) |-> !Y
    );

endmodule
