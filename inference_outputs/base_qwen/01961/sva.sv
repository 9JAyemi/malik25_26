```systemverilog
module and3_not_A_sva (
    input logic A,
    input logic B,
    input logic C,
    output logic X
);
    // No clock or reset signals present in the RTL

    // Combinational logic: X is assigned based on A, B, and C
    // X = !A & (B & C)
    // This logic is always active, so we use @(posedge clk) for consistency

    // Property to check the combinational logic
    comb_logic: assert property (
        @(posedge clk) disable iff (1'b0) X == (~A & (B & C))
    ) else $error("Combinational logic error detected");

endmodule
```