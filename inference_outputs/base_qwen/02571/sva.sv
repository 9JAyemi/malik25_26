```systemverilog
module sky130_fd_sc_hdll__a22o_sva (
    input logic CLK,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    output logic X
);
    // Combinational logic: X is the output of an OR gate with two AND gates as inputs
    // Ensure that X is driven correctly based on the inputs A1, A2, B1, and B2
    combinational_logic: assert property (
        @(posedge CLK) $stable(X) |-> (X == (A1 & A2) | (B1 & B2))
    );
endmodule
```