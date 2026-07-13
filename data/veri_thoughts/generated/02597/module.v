
module and_gate (
    input a,
    input b,
    output out
);

    wire na, nb, nand_out;

    not (na, a);
    not (nb, b);
    nand (nand_out, na, nb);
    not (out, nand_out);

endmodule
