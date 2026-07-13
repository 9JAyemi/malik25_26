module nor2_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B
);
    // Y equals the NOR of A and B.
    check_y_equals_nor: assert property (
        @(posedge clk) Y === ~(A | B)
    );

    // If either input is 1, Y must be 0.
    check_any_input_one_forces_y_zero: assert property (
        @(posedge clk) ((A === 1'b1) || (B === 1'b1)) |-> (Y === 1'b0)
    );

    // If both inputs are 0, Y must be 1.
    check_both_inputs_zero_gives_y_one: assert property (
        @(posedge clk) ((A === 1'b0) && (B === 1'b0)) |-> (Y === 1'b1)
    );

    // If Y is 1, both inputs must be 0.
    check_y_one_implies_inputs_zero: assert property (
        @(posedge clk) (Y === 1'b1) |-> ((A === 1'b0) && (B === 1'b0))
    );

    // If Y is 0, at least one input must be 1.
    check_y_zero_implies_some_input_one: assert property (
        @(posedge clk) (Y === 1'b0) |-> ((A === 1'b1) || (B === 1'b1))
    );
endmodule