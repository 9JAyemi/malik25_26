module mux_2_1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic SEL,
    input logic Y
);

    // Y must always match the mux equation.
    check_mux_function: assert property (
        @(posedge clk) Y === (SEL ? B : A)
    );

    // When SEL is low, Y must equal A.
    check_select_a: assert property (
        @(posedge clk) (SEL === 1'b0) |-> (Y === A)
    );

    // When SEL is high, Y must equal B.
    check_select_b: assert property (
        @(posedge clk) (SEL === 1'b1) |-> (Y === B)
    );

    // If both inputs are equal, Y must equal that common value.
    check_equal_inputs: assert property (
        @(posedge clk) (A === B) |-> (Y === A)
    );

endmodule