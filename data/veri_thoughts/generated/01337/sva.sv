module and_gate_sva (
    input logic clk,   // sampling clock for assertions (DUT has no clock/reset)
    input logic A,
    input logic B,
    input logic X
);
    // X equals A OR B.
    check_x_equals_or: assert property (
        @(posedge clk) X == (A | B)
    );

    // If both inputs are LOW, output is LOW.
    check_x_zero_when_both_zero: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b0)) |-> (X == 1'b0)
    );

    // If A is HIGH, output is HIGH.
    check_x_one_when_a_one: assert property (
        @(posedge clk) (A == 1'b1) |-> (X == 1'b1)
    );

    // If B is HIGH, output is HIGH.
    check_x_one_when_b_one: assert property (
        @(posedge clk) (B == 1'b1) |-> (X == 1'b1)
    );

    // If output is LOW, both inputs are LOW.
    check_inputs_low_when_x_low: assert property (
        @(posedge clk) (X == 1'b0) |-> ((A == 1'b0) && (B == 1'b0))
    );

    // If output is HIGH, at least one input is HIGH.
    check_some_input_high_when_x_high: assert property (
        @(posedge clk) (X == 1'b1) |-> ((A | B) == 1'b1)
    );

    // If inputs are equal, output equals that value (idempotence).
    check_idempotent: assert property (
        @(posedge clk) (A == B) |-> (X == A)
    );
endmodule