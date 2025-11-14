module nor_gate(input a, b, output out);
    wire temp1, temp2, temp3;
    
    nand gate1(temp1, a, a);
    nand gate2(temp2, b, b);
    nand gate3(temp3, temp1, temp2);
    nand gate4(out, temp3, temp3);
endmodule