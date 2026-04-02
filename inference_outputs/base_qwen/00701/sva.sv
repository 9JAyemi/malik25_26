module bin2gray_sva (
  input logic [3:0] binary,
  output logic [3:0] gray
);

  // Binary to Gray conversion logic
  // gray[3] should always be equal to binary[3]
  property p_gray_3;
    @(posedge binary) gray[3] == binary[3];
  endproperty
  assert property (p_gray_3) else $error("gray[3] should be equal to binary[3]");

  // gray[2] should be the XOR of binary[3] and binary[2]
  property p_gray_2;
    @(posedge binary) gray[2] == (binary[3] ^ binary[2]);
  endproperty
  assert property (p_gray_2) else $error("gray[2] should be the XOR of binary[3] and binary[2]");

  // gray[1] should be the XOR of binary[2] and binary[1]
  property p_gray_1;
    @(posedge binary) gray[1] == (binary[2] ^ binary[1]);
  endproperty
  assert property (p_gray_1) else $error("gray[1] should be the XOR of binary[2] and binary[1]");

  // gray[0] should be the XOR of binary[1] and binary[0]
  property p_gray_0;
    @(posedge binary) gray[0] == (binary[1] ^ binary[0]);
  endproperty
  assert property (p_gray_0) else $error("gray[0] should be the XOR of binary[1] and binary[0]");

endmodule