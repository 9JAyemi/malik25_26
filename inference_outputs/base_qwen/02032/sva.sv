```systemverilog
module sky130_fd_sc_ms__o21ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // No clock or reset signals are present in the RTL

    // The logic is purely combinational as there are no sequential elements

    // Key signals: Y, A1, A2, B1, VPWR, VGND, VPB, VNB
    // Interfaces: None

    // Functional behaviors:
    // Y is driven by the output of a NAND gate which takes B1 and the output of an OR gate as inputs
    // The OR gate takes A2 and A1 as inputs

    // Combinational logic assertion
    // Y should be the result of the NAND gate
    combinational_logic: assert property (
        @(posedge VPB) $stable(A1) && $stable(A2) && $stable(B1) |-> Y == ~(B1 & (A2 | A1))
    ) else $error("Combinational logic error: Y does not match the expected value");

endmodule
```