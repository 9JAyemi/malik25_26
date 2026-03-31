module four_input_and_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

// X must equal ~(A & B & C & D).
    check_function_equivalence: assert property (
        @(posedge clk) X == ~(A & B & C & D)
    );

// When all inputs are HIGH, X must be LOW.
    check_all_high_implies_x_low: assert property (
        @(posedge clk) (A && B && C && D) |-> (X == 1'b0)
    );

// If X is HIGH, then not all inputs are HIGH.
    check_x_high_implies_not_all_high: assert property (
        @(posedge clk) (X == 1'b1) |-> !(A && B && C && D)
    );

// If X is LOW, then all inputs are HIGH.
    check_x_low_implies_all_high: assert property (
        @(posedge clk) (X == 1'b0) |-> (A && B && C && D)
    );

// A falling edge on X implies all inputs are HIGH now.
    check_x_fall_implies_all_high_now: assert property (
        @(posedge clk) $fell(X) |-> (A && B && C && D)
    );

// A rising edge on X implies not all inputs are HIGH now.
    check_x_rise_implies_not_all_high_now: assert property (
        @(posedge clk) $rose(X) |-> !(A && B && C && D)
    );

endmodule
