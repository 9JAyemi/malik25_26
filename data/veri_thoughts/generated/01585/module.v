module NAND3 (Y, A, B, C);
    output Y;
    input A, B, C;
    assign Y = ~(A & B & C);
endmodule

module OR2 (Y, A, B);
    output Y;
    input A, B;
    assign Y = A | B;
endmodule

module BUF (Y, A);
    output Y;
    input A;
    assign Y = A;
endmodule

module sky130_fd_sc_hd__o2111ai (
    output Y ,
    input  A1,
    input  A2,
    input  B1,
    input  C1,
    input  D1
);

    // Module supplies
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    // Local signals
    wire or0_out    ;
    wire nand0_out_Y;

    // Instantiation
    OR2 or0 (or0_out, A2, A1);
    NAND3 nand0 (nand0_out_Y, B1, D1, C1);
    BUF buf0 (Y, ~(or0_out & nand0_out_Y));

endmodule