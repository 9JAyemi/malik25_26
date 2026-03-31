```systemverilog
module four_input_and_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    output logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);
    // No clock or reset signals present in the RTL

    // Combinational logic: X is the result of the AND operation on A, B, C, and D
    // Ensure that X is correctly computed based on the inputs
    comb_logic: assert property (
        @(posedge VPB) $stable(A) && $stable(B) && $stable(C) && $stable(D) |-> X == !(A & B & C & D)
    ) else $error("Combinational logic error in four_input_and module");

endmodule
```