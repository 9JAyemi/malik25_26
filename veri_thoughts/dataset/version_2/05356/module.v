
module or_nand_buffer (
    output Y,
    input A1,
    input A2,
    input B1
);

    wire or_out;
    wire nand_out;

    or (or_out, A1, A2);
    nand (nand_out, or_out, B1);
    buf (Y, nand_out);

endmodule