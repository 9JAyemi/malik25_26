```systemverilog
module sky130_fd_sc_hd__o2bb2a_sva (
    input logic X,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // NAND gate output should be the NAND of A2_N and A1_N
    nand_output: assert property (
        @(posedge VPWR) disable iff (VGND) nand0_out |-> (A2_N & A1_N)
    );

    // OR gate output should be the OR of B2 and B1
    or_output: assert property (
        @(posedge VPWR) disable iff (VGND) or0_out |-> (B2 | B1)
    );

    // AND gate output should be the AND of NAND gate output and OR gate output
    and_output: assert property (
        @(posedge VPWR) disable iff (VGND) and0_out_X |-> (nand0_out & or0_out)
    );

    // Buffer output should be the same as AND gate output
    buffer_output: assert property (
        @(posedge VPWR) disable iff (VGND) X |-> (and0_out_X)
    );
endmodule
```