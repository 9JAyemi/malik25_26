```systemverilog
module sky130_fd_sc_hd__o211a_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    output logic X
);
    // The logic is purely combinational as there are no sequential elements.

    // The output X is driven by the expression (A2 OR A1) AND (B1 AND C1).
    // Ensure that the output X is correctly driven by the combinational logic.
    combinational_logic: assert property (
        @(posedge clk) disable iff (!RESETn) (X == (A2 | A1) & (B1 & C1))
    );
endmodule
```