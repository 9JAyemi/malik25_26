module my_module_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    output logic X
);

    ///// Combinational logic /////
    // X is the output of an OR gate with two inputs, which are the outputs of AND gates.
    // The AND gates have different sets of inputs.
    combinational_logic: assert property (
        @(posedge clk) disable iff (!reset_n) (X == (A1 && A2 && A3) || (B1 && B2))
    );

endmodule