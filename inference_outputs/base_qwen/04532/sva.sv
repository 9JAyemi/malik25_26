```systemverilog
module sky130_fd_sc_ms__a21o_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB,
    output logic X
);
    // Combinational logic: X is determined by A1, A2, and B1
    // X = (temp1 & temp2) | (temp3 & temp4)
    // temp1 = ~(A1 & A2)
    // temp2 = A1 ^ B1
    // temp3 = ~B1
    // temp4 = A1
    combinational_logic: assert property (
        @(posedge VPB) disable iff (!VPWR) (X == ((~(A1 & A2)) & (A1 ^ B1)) | ((~B1) & A1))
    );
endmodule
```