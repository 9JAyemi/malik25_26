
module parity_checker (
    input [3:0] IN,
    output OUT,
    input VPWR,
    input VGND,
    input VPB ,
    input VNB 
);

    wire [3:0] nand_out;
    wire [2:0] level1_out;
    wire [1:0] level2_out;
    wire level3_out;

    nand nand1 (nand_out[0], IN[0], IN[1], IN[2]);
    nand nand2 (nand_out[1], IN[1], IN[2], IN[3]);
    nand nand3 (nand_out[2], IN[2], IN[3], IN[0]);
    nand nand4 (nand_out[3], IN[3], IN[0], IN[1]);

    assign level1_out[0] = nand_out[0] & nand_out[1];
    assign level1_out[1] = nand_out[1] & nand_out[2];
    assign level1_out[2] = nand_out[2] & nand_out[3];

    assign level2_out[0] = level1_out[0] & level1_out[1];
    assign level2_out[1] = level1_out[1] & level1_out[2];

    assign level3_out = level2_out[0] & level2_out[1];

    assign OUT = ~level3_out;

endmodule