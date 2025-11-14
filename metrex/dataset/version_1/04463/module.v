module parity_generator_checker #(
  parameter parity_type = "even" // even or odd parity
)
(
  input wire [7:0] data_in,
  input wire parity_in,
  output reg parity_out,
  output reg correct
);

  reg [7:0] temp_data;
  reg [3:0] count;
  reg parity_bit;

  always @(*) begin
    temp_data = data_in ^ (data_in >> 4);
    temp_data = temp_data ^ (temp_data >> 2);
    temp_data = temp_data ^ (temp_data >> 1);
    parity_bit = temp_data[0];

    if (parity_type == "even") begin
      parity_out <= parity_bit;
    end else begin
      parity_out <= ~parity_bit;
    end
  end

  always @(*) begin
    count = data_in[0] + data_in[1] + data_in[2] + data_in[3] + data_in[4] + data_in[5] + data_in[6] + data_in[7] + parity_in;

    if (parity_type == "even") begin
      correct <= (count % 2 == 0);
    end else begin
      correct <= (count % 2 == 1);
    end
  end

endmodule