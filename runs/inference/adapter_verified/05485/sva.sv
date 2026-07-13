module mux2to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic SEL,
    input logic Y
);

// Y must match the RTL mux equation.
    check_mux_equation: assert property (
        @(posedge clk) Y == (SEL ? B : A)
    );

// When SEL is 0, Y must equal A.
    check_select_a: assert property (
        @(posedge clk) (SEL == 1'b0) |-> (Y == A)
    );

// When SEL is 1, Y must equal B.
    check_select_b: assert property (
        @(posedge clk) (SEL == 1'b1) |-> (Y == B)
    );

// If A and B are equal, Y must equal that value regardless of SEL.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (A == B) |-> (Y == A)
    );

endmodule
