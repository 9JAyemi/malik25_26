module or3_4_custom_sva (
    input logic A,
    input logic B,
    input logic C,
    output logic X
);
    // Combinational logic: X is the OR of A, B, and C
    comb_logic: assert property (
        @(posedge clk) disable iff (!reset_n) (X == (A | B | C))
    );
endmodule