module mux_2to1_sva(
    input logic clk,
    input logic A,
    input logic B,
    input logic S,
    input logic MO
);

    // MO must always match the implemented mux expression.
    check_mux_function: assert property (
        @(posedge clk) MO === ((S == 1'b1) ? B : A)
    );

    // When select is low, MO must follow A.
    check_select_low_routes_a: assert property (
        @(posedge clk) (S === 1'b0) |-> (MO === A)
    );

    // When select is high, MO must follow B.
    check_select_high_routes_b: assert property (
        @(posedge clk) (S === 1'b1) |-> (MO === B)
    );

    // If both inputs match, MO must match them regardless of select.
    check_equal_inputs_pass_through: assert property (
        @(posedge clk) (A === B) |-> (MO === A)
    );

endmodule