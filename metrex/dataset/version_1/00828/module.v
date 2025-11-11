
module parity_generator (
  input [15:0] data,
  output [16:0] parity_data
);

  wire parity;

  assign parity = ^data;
  assign parity_data = {parity, data};
  
endmodule