module mux2_sva (
    input logic A0,
    input logic A1,
    input logic S,
    output logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);
    // The logic is purely combinational, so we will use @(posedge VPB) for assertions.

    // The output X should always be either A0 or A1 based on the value of S.
    mux_output: assert property (
        @(posedge VPB) $stable(S) |-> (X == A0) || (X == A1)
    );
endmodule