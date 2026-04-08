module signal_mux_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic X
);

    // X matches the RTL combinational equation.
    check_x_equation: assert property (
        @(posedge clk)
        X == ((A1 & A2) | (~A1 & A3 & B1) | (~A1 & ~A3 & (A2 & B1)))
    );

    // When A1 is high, X follows A2.
    check_a1_high_selects_a2: assert property (
        @(posedge clk)
        A1 |-> (X == A2)
    );

    // When A1 is low, X reduces to B1 AND (A2 OR A3).
    check_a1_low_reduced_form: assert property (
        @(posedge clk)
        (!A1) |-> (X == (B1 & (A2 | A3)))
    );

    // When A1 is low and B1 is low, X must be low.
    check_a1_low_b1_low_forces_zero: assert property (
        @(posedge clk)
        (!A1 && !B1) |-> (X == 1'b0)
    );

    // When A1 is low, B1 is high, and A3 is high, X must be high.
    check_a1_low_b1_high_a3_high_forces_one: assert property (
        @(posedge clk)
        (!A1 && B1 && A3) |-> (X == 1'b1)
    );

    // When A1 is low, B1 is high, and A3 is low, X follows A2.
    check_a1_low_b1_high_a3_low_selects_a2: assert property (
        @(posedge clk)
        (!A1 && B1 && !A3) |-> (X == A2)
    );

endmodule