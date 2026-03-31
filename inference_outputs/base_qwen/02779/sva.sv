```systemverilog
module sky130_fd_sc_lp__a32o_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    output logic X
);
    // The output X is a combinational logic function of the inputs.
    // It is asserted to be 1 if all inputs are 0, otherwise it is 0.
    combinational_logic: assert property (
        @(posedge VPB) disable iff (!VGND) X == (A1 & ~A2 & ~A3 & ~B1 & ~B2 & ~VPWR & ~VGND & ~VPB & ~VNB)
    );
endmodule
```