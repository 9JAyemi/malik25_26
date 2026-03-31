module my_module (
    input [1:0] A1,
    input [1:0] A2,
    input [1:0] B1,
    input [1:0] B2,
    input [1:0] C1,
    input [1:0] VPWR,
    input [1:0] VGND,
    input [1:0] VPB,
    input [1:0] VNB,
    output X
);

wire [1:0] sky130_fd_sc_ms__a221o_1_A1;
wire [1:0] sky130_fd_sc_ms__a221o_1_A2;
wire [1:0] sky130_fd_sc_ms__a221o_1_B1;
wire [1:0] sky130_fd_sc_ms__a221o_1_B2;
wire [1:0] sky130_fd_sc_ms__a221o_1_C1;
wire [1:0] sky130_fd_sc_ms__a221o_1_VPWR;
wire [1:0] sky130_fd_sc_ms__a221o_1_VGND;
wire [1:0] sky130_fd_sc_ms__a221o_1_VPB;
wire [1:0] sky130_fd_sc_ms__a221o_1_VNB;
wire sky130_fd_sc_ms__a221o_1_X;

assign sky130_fd_sc_ms__a221o_1_A1 = A1;
assign sky130_fd_sc_ms__a221o_1_A2 = A2;
assign sky130_fd_sc_ms__a221o_1_B1 = B1;
assign sky130_fd_sc_ms__a221o_1_B2 = B2;
assign sky130_fd_sc_ms__a221o_1_C1 = C1;
assign sky130_fd_sc_ms__a221o_1_VPWR = VPWR;
assign sky130_fd_sc_ms__a221o_1_VGND = VGND;
assign sky130_fd_sc_ms__a221o_1_VPB = VPB;
assign sky130_fd_sc_ms__a221o_1_VNB = VNB;

assign X = ((A1 == B1) && (A2 == B2)) ? 1 : 0;

assign sky130_fd_sc_ms__a221o_1_X = ((C1 == VPWR) && (VPB == VGND)) ? ~sky130_fd_sc_ms__a221o_1_X : sky130_fd_sc_ms__a221o_1_X;

endmodule