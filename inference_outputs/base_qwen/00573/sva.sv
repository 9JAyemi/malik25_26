```systemverilog
module sky130_fd_sc_hd__nor4b_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // The logic is purely combinational as it only uses assign statements.

    // The output Y is the negation of the OR of A, B, C, and D_N.
    combinational_logic: assert property (
        @(posedge VPB) disable iff (!VGND) Y == ~(A | B | C | D_N)
    );
endmodule
```