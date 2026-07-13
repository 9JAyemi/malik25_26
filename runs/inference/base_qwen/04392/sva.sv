module my_module_sva (
    input logic [1:0] A1,
    input logic [1:0] A2,
    input logic [1:0] B1,
    input logic [1:0] B2,
    input logic [1:0] C1,
    input logic [1:0] VPWR,
    input logic [1:0] VGND,
    input logic [1:0] VPB,
    input logic [1:0] VNB,
    output logic X
);

    // The logic is combinational as all operations are done at the same time.

    // A1 and A2 must be equal to B1 and B2 respectively for X to be 1.
    check_A1_A2_B1_B2: assert property (
        @(posedge clk) disable iff (!RESETn) (A1 == B1) && (A2 == B2) |-> X == 1
    ) else $error("A1 and A2 must be equal to B1 and B2 respectively for X to be 1.");

    // C1 must be equal to VPWR and VPB must be equal to VGND for X to be inverted.
    check_C1_VPWR_VPB_VGND: assert property (
        @(posedge clk) disable iff (!RESETn) (C1 == VPWR) && (VPB == VGND) |-> X != sky130_fd_sc_ms__a221o_1_X
    ) else $error("C1 must be equal to VPWR and VPB must be equal to VGND for X to be inverted.");

endmodule