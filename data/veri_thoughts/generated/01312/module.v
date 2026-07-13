
module my_logic (
    output Y,
    input A1,
    input A2,
    input A3,
    input B1,
    input C1,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    // Local signals
    wire or_out;
    wire nand_out_Y;

    // OR gate
    assign or_out = A1 | A2 | A3;

    // NAND gate
    assign nand_out_Y = ~(C1 & or_out & B1);

    // Assign output
    assign Y = nand_out_Y;

endmodule