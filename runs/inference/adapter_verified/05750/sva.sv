module mux_2_1_sva (
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

// When SEL is low, Y must follow A.
    check_select_a: assert property (
        @(posedge clk) !SEL |-> (Y == A)
    );

// When SEL is high, Y must follow B.
    check_select_b: assert property (
        @(posedge clk) SEL |-> (Y == B)
    );

endmodule
