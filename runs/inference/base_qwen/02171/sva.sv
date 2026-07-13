module sky130_fd_sc_ls__a222o_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2,
    output logic X
);
    // Combinational logic: X is the output of an OR gate with three AND gates as inputs.
    // Each AND gate takes two inputs, and the OR gate takes the outputs of these AND gates.
    // The logic is always active, so no clock is needed.
    // No reset signal is present in the RTL.
    // The logic is purely combinational, so we use a clocked assertion to ensure the output is correct at theposedge of a hypothetical clock.
    combinational_logic: assert property (
        @(posedge clk) disable iff (1'b0) (X == (B1 & B2) | (A1 & A2) | (C1 & C2))
    );
endmodule