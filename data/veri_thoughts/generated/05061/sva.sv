module comb_logic_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic X,
    input logic Y
);

    // X must always be the AND of A and B.
    check_x_is_and: assert property (
        @(posedge clk) X == (A & B)
    );

    // Y must always be the XOR of A and B.
    check_y_is_xor: assert property (
        @(posedge clk) Y == (A ^ B)
    );

    // When both inputs are high, X is high and Y is low.
    check_both_high_outputs: assert property (
        @(posedge clk) (A && B) |-> (X && !Y)
    );

    // When both inputs are low, both outputs are low.
    check_both_low_outputs: assert property (
        @(posedge clk) (!A && !B) |-> (!X && !Y)
    );

    // When the inputs differ, X is low and Y is high.
    check_inputs_differ_outputs: assert property (
        @(posedge clk) (A ^ B) |-> (!X && Y)
    );

    // AND and XOR outputs can never both be high.
    check_outputs_not_both_high: assert property (
        @(posedge clk) !(X && Y)
    );

endmodule