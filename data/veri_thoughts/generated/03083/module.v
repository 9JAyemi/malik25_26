module carry_select_adder_32bit (
    input [31:0] A,
    input [31:0] B,
    output [31:0] S,
    output Cout
);

wire [31:0] C0, C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, C12, C13, C14, C15, C16, C17, C18, C19, C20, C21, C22, C23, C24, C25, C26, C27, C28, C29, C30, C31;

assign C0 = A[0] & B[0];
assign C1 = A[1] & B[1];
assign C2 = A[2] & B[2];
assign C3 = A[3] & B[3];
assign C4 = A[4] & B[4];
assign C5 = A[5] & B[5];
assign C6 = A[6] & B[6];
assign C7 = A[7] & B[7];
assign C8 = A[8] & B[8];
assign C9 = A[9] & B[9];
assign C10 = A[10] & B[10];
assign C11 = A[11] & B[11];
assign C12 = A[12] & B[12];
assign C13 = A[13] & B[13];
assign C14 = A[14] & B[14];
assign C15 = A[15] & B[15];
assign C16 = A[16] & B[16];
assign C17 = A[17] & B[17];
assign C18 = A[18] & B[18];
assign C19 = A[19] & B[19];
assign C20 = A[20] & B[20];
assign C21 = A[21] & B[21];
assign C22 = A[22] & B[22];
assign C23 = A[23] & B[23];
assign C24 = A[24] & B[24];
assign C25 = A[25] & B[25];
assign C26 = A[26] & B[26];
assign C27 = A[27] & B[27];
assign C28 = A[28] & B[28];
assign C29 = A[29] & B[29];
assign C30 = A[30] & B[30];
assign C31 = A[31] & B[31];

wire [31:0] P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16, P17, P18, P19, P20, P21, P22, P23, P24, P25, P26, P27, P28, P29, P30, P31;

assign P0 = A[0] ^ B[0];
assign P1 = A[1] ^ B[1];
assign P2 = A[2] ^ B[2];
assign P3 = A[3] ^ B[3];
assign P4 = A[4] ^ B[4];
assign P5 = A[5] ^ B[5];
assign P6 = A[6] ^ B[6];
assign P7 = A[7] ^ B[7];
assign P8 = A[8] ^ B[8];
assign P9 = A[9] ^ B[9];
assign P10 = A[10] ^ B[10];
assign P11 = A[11] ^ B[11];
assign P12 = A[12] ^ B[12];
assign P13 = A[13] ^ B[13];
assign P14 = A[14] ^ B[14];
assign P15 = A[15] ^ B[15];
assign P16 = A[16] ^ B[16];
assign P17 = A[17] ^ B[17];
assign P18 = A[18] ^ B[18];
assign P19 = A[19] ^ B[19];
assign P20 = A[20] ^ B[20];
assign P21 = A[21] ^ B[21];
assign P22 = A[22] ^ B[22];
assign P23 = A[23] ^ B[23];
assign P24 = A[24] ^ B[24];
assign P25 = A[25] ^ B[25];
assign P26 = A[26] ^ B[26];
assign P27 = A[27] ^ B[27];
assign P28 = A[28] ^ B[28];
assign P29 = A[29] ^ B[29];
assign P30 = A[30] ^ B[30];
assign P31 = A[31] ^ B[31];

wire [31:0] G0, G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, G13, G14, G15, G16, G17, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27, G28, G29, G30, G31;

assign G0 = C0 | (P0 & G1);
assign G1 = C1 | (P1 & G2);
assign G2 = C2 | (P2 & G3);
assign G3 = C3 | (P3 & G4);
assign G4 = C4 | (P4 & G5);
assign G5 = C5 | (P5 & G6);
assign G6 = C6 | (P6 & G7);
assign G7 = C7 | (P7 & G8);
assign G8 = C8 | (P8 & G9);
assign G9 = C9 | (P9 & G10);
assign G10 = C10 | (P10 & G11);
assign G11 = C11 | (P11 & G12);
assign G12 = C12 | (P12 & G13);
assign G13 = C13 | (P13 & G14);
assign G14 = C14 | (P14 & G15);
assign G15 = C15 | (P15 & G16);
assign G16 = C16 | (P16 & G17);
assign G17 = C17 | (P17 & G18);
assign G18 = C18 | (P18 & G19);
assign G19 = C19 | (P19 & G20);
assign G20 = C20 | (P20 & G21);
assign G21 = C21 | (P21 & G22);
assign G22 = C22 | (P22 & G23);
assign G23 = C23 | (P23 & G24);
assign G24 = C24 | (P24 & G25);
assign G25 = C25 | (P25 & G26);
assign G26 = C26 | (P26 & G27);
assign G27 = C27 | (P27 & G28);
assign G28 = C28 | (P28 & G29);
assign G29 = C29 | (P29 & G30);
assign G30 = C30 | (P30 & G31);
assign G31 = C31;

assign S = P0 ^ G0;
assign Cout = G31;

endmodule