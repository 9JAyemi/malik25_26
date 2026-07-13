
module DivSelSlice (DivLenSel, DNB, DSN, Division);
input [3:0] DivLenSel; 
input [8:0] DNB, DSN;
output [8:0] Division;
wire [1:0] BDivLenSel; 

// Buffers for DivLenSel
assign BDivLenSel[0] = DivLenSel[0];
assign BDivLenSel[1] = DivLenSel[1];

// Instantiate the 2-bit multiplexers
MUX2B mux0 (DNB[0], DSN[0], BDivLenSel[0], Division[0]);
MUX2B mux1 (DNB[1], DSN[1], BDivLenSel[0], Division[1]);
MUX2B mux2 (DNB[2], DSN[2], BDivLenSel[1], Division[2]);
MUX2B mux3 (DNB[3], DSN[3], BDivLenSel[1], Division[3]);
MUX2B mux4 (DNB[4], DSN[4], DivLenSel[2], Division[4]); 
MUX2B mux5 (DNB[5], DSN[5], DivLenSel[2], Division[5]); 
MUX2B mux6 (DNB[6], DSN[6], DivLenSel[3], Division[6]); 
MUX2B mux7 (DNB[7], DSN[7], DivLenSel[3], Division[7]); 
MUX2B mux8 (DNB[8], DSN[8], DivLenSel[3], Division[8]); 

endmodule
module MUX2B (A, B, S, Y); 
input A, B;
input S;
output Y;
wire A_not, B_not;

// Invert the inputs
assign A_not = ~A;
assign B_not = ~B;

// Implement the multiplexer using AND-OR gates
assign Y = (A & S) | (B & A_not);

endmodule