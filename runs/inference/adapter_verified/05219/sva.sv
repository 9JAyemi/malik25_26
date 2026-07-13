module xor_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic X,
    input logic VPWR,
    input logic VGND
);

// X must equal A ^ B.
    check_xor_function: assert property (
        @(posedge clk) X == (A ^ B)
    );

// When A and B are equal, X must be 0.
    check_equal_inputs_zero: assert property (
        @(posedge clk) (A == B) |-> (X == 1'b0)
    );

// When A and B differ, X must be 1.
    check_different_inputs_one: assert property (
        @(posedge clk) (A != B) |-> (X == 1'b1)
    );

// A rising edge on B must drive X high.
    check_b_rise_sets_x: assert property (
        @(posedge clk) $rose(B) |-> (X == 1'b1)
    );

// A falling edge on B must drive X low.
    check_b_fall_clears_x: assert property (
        @(posedge clk) $fell(B) |-> (X == 1'b0)
    );

// A rising edge on A must drive X high.
    check_a_rise_sets_x: assert property (
        @(posedge clk) $rose(A) |-> (X == 1'b1)
    );

// A falling edge on A must drive X low.
    check_a_fall_clears_x: assert property (
        @(posedge clk) $fell(A) |-> (X == 1'b0)
    );

endmodule
