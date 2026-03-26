module mux_2_1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic S,
    input logic MO
);

    // MO must select A when S is low.
    check_select_a: assert property (
        @(posedge clk) (S == 1'b0) |-> (MO == A)
    );

    // MO must select B when S is high.
    check_select_b: assert property (
        @(posedge clk) (S == 1'b1) |-> (MO == B)
    );

    // MO must match the implemented mux equation.
    check_mux_equation: assert property (
        @(posedge clk) MO == (((~S) & A) | (S & B))
    );

    // If both inputs are equal, MO must equal that value.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (A == B) |-> (MO == A)
    );

endmodule