module barrel_shifter (
  input [31:0] data_in,
  input [4:0] shift_amount,
  output [31:0] data_out,
  output zero_flag
);

  reg [31:0] shifted_data;
  wire [31:0] mux_input [0:31];
  wire [4:0] shift_amount_inv;
  wire [4:0] shift_amount_inv_plus_one;

  assign shift_amount_inv = ~shift_amount;
  assign shift_amount_inv_plus_one = shift_amount_inv + 1;

  // Generate all possible shift amounts
  assign mux_input[0] = data_in;
  generate
    genvar i;
    for (i = 1; i < 32; i = i + 1) begin
      assign mux_input[i] = {mux_input[i-1][shift_amount_inv_plus_one-1:0], mux_input[i-1][31:shift_amount_inv_plus_one]};
    end
  endgenerate

  // Select the output based on the shift amount
  assign data_out = mux_input[shift_amount];

  // Check if the output is zero
  assign zero_flag = (data_out == 0);

endmodule