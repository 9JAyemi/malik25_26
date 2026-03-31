```systemverilog
module sky130_fd_sc_hs__nand2b_sva (
    input logic A_N,
    input logic B,
    input logic VPWR,
    input logic VGND,
    output logic Y
);
    // The logic is purely combinational as it only involves assign statements.

    // Y is the output of the NAND gate, which is a combinational function of A_N and B.
    // Y should be LOW when both A_N and B are HIGH, and HIGH otherwise.
    combinational_logic: assert property (
        @(posedge VPWR) disable iff (!VGND) (A_N == 1'b1 && B == 1'b1) |-> (Y == 1'b0)
    );
    combinational_logic_2: assert property (
        @(posedge VPWR) disable iff (!VGND) !(A_N == 1'b1 && B == 1'b1) |-> (Y == 1'b1)
    );
endmodule
```