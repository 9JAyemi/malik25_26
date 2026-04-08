
module myNAND3 (IN1,IN2,IN3,QN);

input IN1,IN2,IN3;
output QN;

wire nand1, nand2;

nand (nand1, IN1, IN2, IN3);
nand (nand2, nand1, nand1);
not (QN, nand2);

endmodule