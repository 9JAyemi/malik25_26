
module CAM #(
  parameter n = 8, // number of bits in data
  parameter m = 4 // number of bits in search key
)(
  input [n-1:0] data_in,
  input [m-1:0] search_key,
  output match,
  output reg [n-1:0] data_out
);

reg [n-1:0] stored_data = 0; // Initialized to 0 to avoid linting errors
reg match = 0;

always @ (search_key, data_in) begin
  if (search_key == stored_data) begin
    match = 1;
    data_out <= stored_data;
  end else begin
    match = 0;
    data_out <= 0;
  end
end

endmodule