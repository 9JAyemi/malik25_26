module MUX_2x1_8_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic SEL,
    input logic [7:0] X
);

    // X must always match the mux select function.
    check_mux_function: assert property (
        @(posedge clk) X === (SEL ? B : A)
    );

    // When SEL is low, X must route A.
    check_sel_low_routes_a: assert property (
        @(posedge clk) (SEL == 1'b0) |-> (X === A)
    );

    // When SEL is high, X must route B.
    check_sel_high_routes_b: assert property (
        @(posedge clk) (SEL == 1'b1) |-> (X === B)
    );

    // If both inputs are equal, X must equal that common value.
    check_equal_inputs_same_output: assert property (
        @(posedge clk) (A === B) |-> (X === A)
    );

    // Stable inputs and select must keep the output stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) $stable({A, B, SEL}) |-> $stable(X)
    );

endmodule