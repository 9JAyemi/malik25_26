
module mux2to1 (A, B, S, Z);
input A, B, S;
output Z;

buf buf_A (Z, S ? B : A);

endmodule