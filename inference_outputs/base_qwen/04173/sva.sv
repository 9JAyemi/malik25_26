```systemverilog
module logic_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    output logic X
);
    // Combinational logic: X is determined by the inputs A1, A2, B1, and B2.
    // X = (A1 | A2) & (~B1 | B2) & (~A1 | ~A2 | B1)
    combinational_logic: assert property (
        @(posedge VPWR) disable iff (!VGND) (X == ((A1 | A2) & (~B1 | B2) & (~A1 | ~A2 | B1)))
    );
endmodule
```