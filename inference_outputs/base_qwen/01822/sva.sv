```systemverilog
module sky130_fd_sc_ms__o211ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // The logic is purely combinational as there are no sequential elements.

    // The output Y is driven by the combination of A1, A2, B1, and C1.
    // Y = C1 & (A1 | A2) & B1

    // Property to check the combinational logic for Y
    combinational_logic: assert property (
        @(posedge VPWR) disable iff (VGND) (Y == (C1 & (A1 | A2) & B1))
    ) else $error("Combinational logic for Y is incorrect");

endmodule
```