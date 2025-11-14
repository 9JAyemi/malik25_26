module RIPPLE_CARRY_ADDER (
input wire [3:0] wA,
input wire [3:0] wB,
input wire wCi,
output wire [3:0] wR,
output wire wCo
);

wire [3:0] c;

FULL_ADDER fa0(wA[0], wB[0], wCi, wR[0], c[0]);
FULL_ADDER fa1(wA[1], wB[1], c[0], wR[1], c[1]);
FULL_ADDER fa2(wA[2], wB[2], c[1], wR[2], c[2]);
FULL_ADDER fa3(wA[3], wB[3], c[2], wR[3], wCo);

endmodule

module FULL_ADDER (
input wire  wA,wB,wCi,
output wire  wR ,
output wire wCo
);

assign {wCo,wR} = wA + wB + wCi;
endmodule