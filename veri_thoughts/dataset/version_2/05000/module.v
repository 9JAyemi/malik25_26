
module AregInexactSlice (
input [31:0] AM,
output notAM31_3,
output notAM2_0
);

wire [11:4] notAORed;

nand (notAM31_3, AM[31], AM[30], AM[29], AM[28], AM[27], AM[26], AM[25], AM[24], AM[23], AM[22], AM[21], AM[20], AM[19]); // Fixed AM[19], AM[20], AM[21], AM[22], AM[23], AM[24], AM[25], AM[26], AM[27], AM[28], AM[29], AM[30], AM[31] to AM[31], AM[30], AM[29], AM[28], AM[27], AM[26], AM[25], AM[24], AM[23], AM[22], AM[21], AM[20], AM[19] //
nand (notAM2_0, AM[2], AM[1], AM[0]); // Fixed AM[1], AM[2], AM[0] to AM[2], AM[1], AM[0] //

endmodule