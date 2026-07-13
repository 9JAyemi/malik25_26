module inverter_sva (
    input logic clk,
    input logic I,
    input logic O
);

// Output is always the bitwise inversion of the input.
    check_inverter_inversion: assert property (
        @(posedge clk) O == ~I
    );

endmodule
module and_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Y
);

// Output is always the bitwise AND of the two inputs.
    check_and_function: assert property (
        @(posedge clk) Y == (A & B)
    );

endmodule
module mux_2to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);

// When select is low, output follows A.
    check_mux_select_a: assert property (
        @(posedge clk) !S |-> (Y == A)
    );

// When select is high, output follows B.
    check_mux_select_b: assert property (
        @(posedge clk) S |-> (Y == B)
    );

// When both inputs are equal, output matches that value.
    check_mux_equal_inputs: assert property (
        @(posedge clk) (A == B) |-> (Y == A)
    );

endmodule
