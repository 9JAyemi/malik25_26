module hamming_encoder_decoder (
  input [k-1:0] data_in,
  output [n-1:0] encoded_data,
  output [k-1:0] decoded_data
);

parameter k = 4; // length of input data
parameter n = 7; // length of encoded data

// Calculate the parity bits for the encoded data
wire p1, p2, p3;
assign p1 = data_in[0] ^ data_in[1] ^ data_in[3];
assign p2 = data_in[0] ^ data_in[2] ^ data_in[3];
assign p3 = data_in[1] ^ data_in[2] ^ data_in[3];

// Append the parity bits to the input data to create the encoded data
assign encoded_data = {data_in, p1, p2, p3};

// Calculate the syndrome of the encoded data
wire s1, s2, s3;
assign s1 = encoded_data[0] ^ encoded_data[1] ^ encoded_data[3] ^ encoded_data[4] ^ encoded_data[6];
assign s2 = encoded_data[0] ^ encoded_data[2] ^ encoded_data[3] ^ encoded_data[5] ^ encoded_data[6];
assign s3 = encoded_data[1] ^ encoded_data[2] ^ encoded_data[3] ^ encoded_data[6];

// Correct any single-bit errors in the encoded data
wire [n-1:0] corrected_data;
assign corrected_data = encoded_data;
assign corrected_data[s1 + s2*2 + s3*4 - 1] = ~corrected_data[s1 + s2*2 + s3*4 - 1];

// Extract the original input data from the corrected data
assign decoded_data = {corrected_data[3], corrected_data[5], corrected_data[6], corrected_data[4]};

endmodule