```systemverilog
module sky130_fd_sc_ms__o31ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // No clock or reset signals are present in the RTL

    // The logic is purely combinational as there are no sequential elements

    // Key signals and functional behaviors:
    // Y is the output of a buffer that drives the result of a NAND gate
    // The NAND gate takes the output of an OR gate as one input and B1 as the other
    // The OR gate takes A2, A1, and A3 as inputs

    // Combinational logic assertion
    // Y should be the result of the NAND gate
    combinational_logic: assert property (
        @(posedge VPWR) disable iff (VGND) (Y == ~(A2 | A1 | A3) & B1)
    );
endmodule
```