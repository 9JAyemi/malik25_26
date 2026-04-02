module and_gate_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic X,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // The output X is the result of the AND operation on A1, A2, and B1, with VPWR as a condition.
    and_operation: assert property (
        @(posedge VPWR) $stable(A1) && $stable(A2) && $stable(B1) |-> X == (A1 & A2 & B1)
    );
endmodule