module mux_2to1_enable_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic EN,
    input logic Y
);

// Y must match the RTL mux equation.
    check_mux_equation: assert property (
        @(posedge clk) Y == (EN ? A : B)
    );

// When EN is high, Y must follow A.
    check_select_a_when_en_high: assert property (
        @(posedge clk) EN |-> (Y == A)
    );

// When EN is low, Y must follow B.
    check_select_b_when_en_low: assert property (
        @(posedge clk) !EN |-> (Y == B)
    );

endmodule
