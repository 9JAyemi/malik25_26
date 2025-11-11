
module xnor_nand( 
    input a, 
    input b, 
    output out );

    wire nand1, nand2, nand3;

    nand n1(nand1, a, b);
    nand n2(nand2, a, nand1);
    nand n3(nand3, b, nand1);
    nand n4(out, nand2, nand3);

endmodule