```systemverilog
module my_module_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    output logic X
);
    // Combinational logic: X is determined by the inputs A1, A2, A3, and B1
    // X is 1 if (A1 & ~A2) | (A2 & ~A1 & A3 & ~B1) | (~A1 & ~A2 & ~A3 & B1)
    // X is 0 otherwise
    combinational_logic: assert property (
        @(posedge clk) disable iff (!reset_n) (X == ((A1 & ~A2) | (A2 & ~A1 & A3 & ~B1) | (~A1 & ~A2 & ~A3 & B1)))
    );
endmodule
```