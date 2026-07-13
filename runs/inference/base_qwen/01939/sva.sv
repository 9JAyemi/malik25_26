module my_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    output logic X
);
    // Combinational logic: X is the result of a combination of A1, A2, B1, and B2
    // X = (A1 & A2) & ~(B1 & B2)
    combinational_logic: assert property (
        @(posedge clk) disable iff (!reset_n) (X == (A1 & A2) & ~(B1 & B2))
    );
endmodule