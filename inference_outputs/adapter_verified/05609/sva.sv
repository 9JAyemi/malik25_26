module four_input_and_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic C1,
    input logic X
);

// X equals A1 & A2 & ~B1_N.
    check_function_equivalence: assert property (
        @(posedge clk) X == (A1 & A2 & ~B1_N)
    );

// When A1 is 0, X must be 0.
    check_a1_zero_forces_x_zero: assert property (
        @(posedge clk) (A1 == 1'b0) |-> (X == 1'b0)
    );

// When A2 is 0, X must be 0.
    check_a2_zero_forces_x_zero: assert property (
        @(posedge clk) (A2 == 1'b0) |-> (X == 1'b0)
    );

// When B1_N is 1, X must be 0.
    check_b1n_one_forces_x_zero: assert property (
        @(posedge clk) (B1_N == 1'b1) |-> (X == 1'b0)
    );

// When A1=1, A2=1, and B1_N=0, X must be 1.
    check_all_inputs_enable_x: assert property (
        @(posedge clk) (A1 && A2 && !B1_N) |-> (X == 1'b1)
    );

// X can only be 1 when A1=1, A2=1, and B1_N=0.
    check_x_one_implies_inputs: assert property (
        @(posedge clk) (X == 1'b1) |-> (A1 && A2 && !B1_N)
    );

endmodule
