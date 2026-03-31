module mux2to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic SEL,
    input logic Y
);

    // When SEL is 0, Y must match A.
    check_select_a: assert property (
        @(posedge clk) (SEL === 1'b0) |-> (Y === A)
    );

    // When SEL is not 0, Y must match B.
    check_select_b: assert property (
        @(posedge clk) (SEL !== 1'b0) |-> (Y === B)
    );

endmodule