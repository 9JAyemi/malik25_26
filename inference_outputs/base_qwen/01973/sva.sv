```systemverilog
module sky130_fd_sc_lp__o31a_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    output logic X
);
    // The logic is purely combinational as there are no sequential elements.

    // The clock and reset signals are not present in the RTL.

    // Key signals and interfaces:
    // A1, A2, A3, B1 are inputs
    // X is the output

    // Functional behaviors:
    // X is the result of the expression (A2 OR A1 OR A3) AND B1

    // Combinational logic assertion
    // X should be 1 if (A2 OR A1 OR A3) AND B1 is 1, otherwise X should be 0
    combinational_logic: assert property (
        @(posedge clk) disable iff (!RESETn) (X == ((A2 | A1 | A3) & B1))
    ) else $error("Combinational logic error detected");

endmodule
```