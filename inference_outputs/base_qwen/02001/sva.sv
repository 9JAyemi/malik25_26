```systemverilog
module nor4b_sva (
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
    // No clock or reset signals are present.

    // Check that Y is the NOR of A, B, C, and D_N
    nor_behavior: assert property (
        @(posedge VPWR) disable iff (!VGND) (Y == ~(A | B | C | D_N))
    );
endmodule
```