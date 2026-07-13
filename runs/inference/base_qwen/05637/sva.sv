module and4b_sva (
    input logic A_N,
    input logic B,
    input logic C,
    input logic D,
    output logic X
);
    // Combinational logic: X is the negation of the OR of A_N, B, C, and D
    comb_logic: assert property (
        @(posedge clk) disable iff (!reset_n) (X == ~(A_N | B | C | D))
    );
endmodule