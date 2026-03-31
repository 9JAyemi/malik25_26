```systemverilog
module multi_input_module_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1,
    output logic X
);
    // Combinational logic: X is a function of A1, A2, A3, A4, and B1
    // X is asserted when any combination of A1, A2, A3, A4, and B1 is true
    comb_logic: assert property (
        @(posedge clk) disable iff (!RESETn) (X == ((A1&A2&A3) | (A1&A2&A4) | (A1&A3&A4) | (A2&A3&A4) | (A1&A2&B1) | (A1&A3&B1) | (A1&A4&B1) | (A2&A3&B1) | (A2&A4&B1) | (A3&A4&B1)))
    );
endmodule
```