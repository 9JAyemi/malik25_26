
module OAI21B2HD4X (AN, BN, C, Z);

input AN;
input BN;
input C;

output Z;

wire I0_out;
wire I1_out;

and I0 (I0_out, AN, BN);
not I1 (I1_out, I0_out);
and I2 (Z, I1_out, C);

endmodule