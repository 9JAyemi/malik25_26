module mux2i_sva (
    input logic clk,
    input logic Y,
    input logic A0,
    input logic A1,
    input logic S
);

    // Output must always match the implemented mux expression.
    check_mux_function: assert property (
        @(posedge clk) Y === (S ? A1 : A0)
    );

    // When select is low, the output must follow A0.
    check_select_low_routes_a0: assert property (
        @(posedge clk) (S === 1'b0) |-> (Y === A0)
    );

    // When select is high, the output must follow A1.
    check_select_high_routes_a1: assert property (
        @(posedge clk) (S === 1'b1) |-> (Y === A1)
    );

    // If both inputs are equal, the output must equal that same value.
    check_equal_inputs_same_output: assert property (
        @(posedge clk) (A0 === A1) |-> (Y === A0)
    );

    // If all inputs are stable, the output must remain stable.
    check_stable_inputs_stable_output: assert property (
        @(posedge clk) ($stable(A0) && $stable(A1) && $stable(S)) |-> $stable(Y)
    );

    // With select held low and A0 stable, changes on A1 must not affect Y.
    check_a1_masked_when_select_low: assert property (
        @(posedge clk) ((S === 1'b0) && $stable(S) && $stable(A0)) |-> $stable(Y)
    );

    // With select held high and A1 stable, changes on A0 must not affect Y.
    check_a0_masked_when_select_high: assert property (
        @(posedge clk) ((S === 1'b1) && $stable(S) && $stable(A1)) |-> $stable(Y)
    );

endmodule