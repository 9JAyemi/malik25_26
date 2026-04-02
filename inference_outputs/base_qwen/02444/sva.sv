module my_buffer_sva (
    input logic A,
    input logic Z,
    input logic TE_B,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);
    // TE_B can only transition from LOW to HIGH when A is HIGH.
    TE_B_high: assert property (
        @(posedge VPB) disable iff (!VPWR) $rose(TE_B) |-> (A == 1'b1)
    );
    // TE_B can only transition from HIGH to LOW when A is LOW.
    TE_B_low: assert property (
        @(posedge VPB) disable iff (!VPWR) $fell(TE_B) |-> (A == 1'b0)
    );
    // Z is driven to 1'b0 when TE_B is LOW.
    Z_low: assert property (
        @(posedge VPB) disable iff (!VPWR) TE_B == 1'b0 |-> Z == 1'b0
    );
    // Z is driven to the value of A when TE_B is HIGH.
    Z_high: assert property (
        @(posedge VPB) disable iff (!VPWR) TE_B == 1'b1 |-> Z == A
    );
endmodule