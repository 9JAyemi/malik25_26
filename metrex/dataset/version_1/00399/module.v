module nfc_transmitter (
  input clk,
  input data_in,
  output reg en,
  output reg carrier_out
);

reg [31:0] counter;
reg carrier_gen;

always @(posedge clk) begin
  counter <= counter + 1;
  carrier_gen <= ~carrier_gen;
  en <= data_in;
  if (en) begin
    carrier_out <= carrier_gen;
  end else begin
    carrier_out <= 1'b0;
  end
end

endmodule

module nfc_receiver (
  input clk,
  input carrier_in,
  output reg data_out,
  output reg valid_out
);

reg [31:0] counter;
reg carrier_gen;
reg prev_carrier_in;

always @(posedge clk) begin
  counter <= counter + 1;
  carrier_gen <= ~carrier_gen;
  prev_carrier_in <= carrier_in;

  if (carrier_in != prev_carrier_in) begin
    valid_out <= 1'b1;
    data_out <= carrier_gen;
  end else begin
    valid_out <= 1'b0;
    data_out <= 1'b0;
  end
end

endmodule