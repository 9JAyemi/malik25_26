module my_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    output logic X
);
    // Combinational logic: X is driven by the OR of (A1 AND A2) and C1, B1
    comb_logic: assert property (
        @(posedge clk) disable iff (!reset_n) (X == (A1 && A2) || C1 || B1)
    );
endmodule