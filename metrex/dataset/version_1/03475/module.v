module CryptoBlock (
  input [m-1:0] plaintext,
  input [k-1:0] key,
  input [m-1:0] ciphertext,
  input [m-1:0] message,
  output [m-1:0] ciphertext_out,
  output [m-1:0] plaintext_out,
  output [n-1:0] hash_out
);

parameter k = 128; // length of secret key in bits
parameter m = 256; // length of message in bits
parameter n = 256; // length of hash in bits

assign ciphertext_out = plaintext ^ key;

assign plaintext_out = ciphertext ^ key;

assign hash_out = message;

endmodule