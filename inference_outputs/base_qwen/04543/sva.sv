```systemverilog
module my_nand2b_sva (
    input logic Y,
    input logic A_N,
    input logic B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // No clock or reset signals present in the RTL

    // Combinational logic: Y = ~(~B & ~A_N)
    // Assert that Y is the correct output of the NAND2 gate
    nand2_output: assert property (
        @(posedge VPWR) disable iff (VGND) (Y == ~(~B & ~A_N))
    );
endmodule
```