module mux_2to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic SEL,
    input logic Y
);

    // Y must follow A when SEL is low.
    check_sel_low_routes_a: assert property (
        @(posedge clk) !SEL |-> (Y == A)
    );

    // Y must follow B when SEL is high.
    check_sel_high_routes_b: assert property (
        @(posedge clk) SEL |-> (Y == B)
    );

    // Y must always match the mux select equation.
    check_mux_equation: assert property (
        @(posedge clk) Y == (SEL ? B : A)
    );

endmodule