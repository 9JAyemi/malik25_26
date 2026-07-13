module sky130_fd_sc_hd__nor4_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // The logic is purely combinational as there are no sequential elements.

    // The output Y is the result of a NOR operation on inputs A, B, C, and D.
    // NOR operation: Y = ~(A | B | C | D)
    combinational_logic: assert property (
        @(posedge VPWR) disable iff (VGND) (Y == ~(A | B | C | D))
    );
endmodule