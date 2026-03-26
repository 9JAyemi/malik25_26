module mux_2to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);

    // Y must implement the 2:1 mux equation.
    check_mux_equation: assert property (
        @(posedge clk) Y == ((~S & A) | (S & B))
    );

    // When S is low, Y must select A.
    check_select_a: assert property (
        @(posedge clk) !S |-> (Y == A)
    );

    // When S is high, Y must select B.
    check_select_b: assert property (
        @(posedge clk) S |-> (Y == B)
    );

    // If both inputs are equal, Y must match that value.
    check_equal_inputs: assert property (
        @(posedge clk) (A == B) |-> (Y == A)
    );

    // With A=0 and B=1, Y must follow S.
    check_follow_s: assert property (
        @(posedge clk) (A == 1'b0 && B == 1'b1) |-> (Y == S)
    );

    // With A=1 and B=0, Y must follow inverted S.
    check_follow_not_s: assert property (
        @(posedge clk) (A == 1'b1 && B == 1'b0) |-> (Y == ~S)
    );

endmodule