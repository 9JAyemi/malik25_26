module my_or4b_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N
);
    // No clock or reset signals are present in the RTL

    // Combinational logic: X is the output of a buffer
    // The buffer's input is the output of an OR gate
    // The OR gate's inputs are the output of a NOT gate and the inputs A, B, and C
    // The NOT gate's input is D_N
    // The buffer's output is X

    // Combinational logic assertion
    // X should be the same as the output of the OR gate
    // The OR gate's output is the OR of not0_out, C, B, and A
    // not0_out is the NOT of D_N
    // Therefore, X should be the OR of ~D_N, C, B, and A
    comb_logic: assert property (
        @(posedge clk) disable iff (!RESETn) X == (A | B | C | ~D_N)
    );
endmodule