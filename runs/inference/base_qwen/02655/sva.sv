module or4_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    output logic X
);
    // Combinational logic, so use @(posedge clk)
    // The output X should always be the OR of A, B, C, and D
    comb_logic: assert property (
        @(posedge VPB) disable iff (!VGND) (X == (A | B | C | D))
    );
endmodule