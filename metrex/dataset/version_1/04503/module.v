module ASHIFTER_32bit(S, D, C);

input [31:0] D;
input C;
output [31:0] S;

wire C1;
wire [61:0]w;
wire G; 



not not1(C1,C);

and and0 (w[0], D[0],C);
and and1 (S[0], D[1],C1);
and and2 (w[2], D[1],C);
and and3 (w[3], D[2],C1);
and and4 (w[4], D[2],C);
and and5 (w[5], D[3],C1);
and and6 (w[6], D[3],C);
and and7 (w[7], D[4],C1);
and and8 (w[8], D[4],C);
and and9 (w[9], D[5],C1);
and and10(w[10], D[5],C);
and and11(w[11], D[6],C1);
and and11(w[12], D[6],C);
and and13(w[13], D[7],C1);
and and14 (w[14], D[7],C);
and and15(w[15], D[8],C1);
and and16(w[16], D[8],C);
and and17(w[17], D[9],C1);
and and18(w[18], D[9],C);
and and19(w[19], D[10],C1);
and and20(w[20], D[10],C);
and and21(w[21], D[11],C1);
and and22(w[22], D[11],C);
and and23(w[23], D[12],C1);
and and24(w[24], D[12],C);
and and25(w[25], D[13],C1);
and and26(w[26], D[13],C);
and and27(w[27], D[14],C1);
and and28(w[28], D[14],C);
and and29(w[29], D[15],C1);
and and30(w[30], D[15],C);
and and31(w[31], D[16],C1);
and and32(w[32], D[16],C);
and and33(w[33], D[17],C1);
and and34(w[34], D[17],C);
and and35(w[35], D[18],C1);
and and36(w[36], D[18],C);
and and37(w[37], D[19],C1);
and and38(w[38], D[19],C);
and and39(w[39], D[20],C1);
and and40(w[40], D[20],C);
and and41(w[41], D[21],C1);
and and42(w[42], D[21],C);
and and43(w[43], D[22],C1);
and and44(w[44], D[22],C);
and and45(w[45], D[23],C1);
and and46(w[46], D[23],C);
and and47(w[47], D[24],C1);
and and48(w[48], D[24],C);
and and49(w[49], D[25],C1);
and and50(w[50], D[25],C);
and and51(w[51], D[26],C1);
and and52(w[52], D[26],C);
and and53(w[53], D[27],C1);
and and54(w[54], D[27],C);
and and55(w[55], D[28],C1);
and and56(w[56], D[28],C);
and and57(w[57], D[29],C1);
and and58(w[58], D[29],C);
and and59(w[59], D[30],C1);
and and60(S[31], D[31],C);
and and61(w[61], D[31],C1);





or or1 (S[1], w[0], w[3]);
or or2 (S[2], w[2], w[5]);
or or3 (S[3], w[4], w[7]);
or or4 (S[4], w[6], w[9]);
or or5 (S[5], w[8], w[11]);
or or6 (S[6], w[10], w[13]);
or or7(S[7], w[12], w[15]);
or or8 (S[8], w[14], w[17]);
or or9 (S[9], w[16], w[19]);
or or10 (S[10], w[18], w[21]);
or or11 (S[11], w[20], w[23]);
or or12 (S[12], w[22], w[25]);
or or13(S[13], w[24], w[27]);
or or14(S[14], w[26], w[29]);
or or15(S[15], w[28], w[31]);
or or16(S[16], w[30], w[33]);
or or17(S[17], w[32], w[35]);
or or18(S[18], w[34], w[37]);
or or19(S[19], w[36], w[39]);
or or20(S[20], w[38], w[41]);
or or21(S[21], w[40], w[43]);
or or22(S[22], w[42], w[45]);
or or23(S[23], w[44], w[47]);
or or24(S[24], w[46], w[49]);
or or25(S[25], w[48], w[51]);
or or26(S[26], w[50], w[53]);
or or27(S[27], w[52], w[55]);
or or28(S[28], w[54], w[57]);
or or29(S[29], w[56], w[59]);
or or30(S[30], w[58], w[61]);





endmodule
