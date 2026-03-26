module three_input_module_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1
);

    // X matches the implemented combinational function.
    check_x_matches_function: assert property (
        @(posedge clk)
        X == (A1 ? (~B1) : (A2 ? B1 : 1'b0))
    );

    // When A1 is high, X inverts B1.
    check_x_inverts_b1_when_a1_high: assert property (
        @(posedge clk)
        A1 |-> (X == (~B1))
    );

    // When A1 is low, X reduces to A2 AND B1.
    check_x_is_a2_and_b1_when_a1_low: assert property (
        @(posedge clk)
        (!A1) |-> (X == (A2 & B1))
    );

    // When A2 is low, X reduces to A1 AND not B1.
    check_x_is_a1_and_not_b1_when_a2_low: assert property (
        @(posedge clk)
        (!A2) |-> (X == (A1 & (~B1)))
    );

    // When only A2 is high, X equals B1.
    check_x_follows_b1_when_only_a2_high: assert property (
        @(posedge clk)
        (!A1 && A2) |-> (X == B1)
    );

    // When A1 and A2 are both low, X is low.
    check_x_low_when_a1_a2_low: assert property (
        @(posedge clk)
        (!A1 && !A2) |-> (X == 1'b0)
    );

    // When A1 is low and B1 is high, X equals A2.
    check_x_follows_a2_when_a1_low_b1_high: assert property (
        @(posedge clk)
        (!A1 && B1) |-> (X == A2)
    );

endmodule