module sky130_fd_sc_hd__xor2_sva (
    input logic CLK,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic A,
    input logic B,
    output logic X
);
    // XOR logic must produce the correct output based on inputs A and B
    xor_logic: assert property (
        @(posedge CLK) disable iff (!VPWR || !VGND) (X == A ^ B)
    );
endmodule