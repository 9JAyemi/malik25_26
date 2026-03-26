module my_mux_2to1_sva (
    input logic clk,
    input logic OUT,
    input logic A,
    input logic B,
    input logic SEL
);

    // When SEL is low, OUT must follow A.
    check_sel_low_routes_a: assert property (
        @(posedge clk) (SEL == 1'b0) |-> (OUT == A)
    );

    // When SEL is high, OUT must follow B.
    check_sel_high_routes_b: assert property (
        @(posedge clk) (SEL == 1'b1) |-> (OUT == B)
    );

    // When both inputs are equal, OUT must match that common value.
    check_equal_inputs_pass_through: assert property (
        @(posedge clk) (A == B) |-> (OUT == A)
    );

    // OUT must match the implemented 2:1 mux equation.
    check_mux_boolean_equation: assert property (
        @(posedge clk) OUT == ((A & ~SEL) | (B & SEL))
    );

endmodule