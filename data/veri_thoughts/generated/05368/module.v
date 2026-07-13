
module shift_register(
  input clk,
  input reset,
  input load,
  input [2:0] load_data,
  output serial_out
);

  reg [2:0] reg_data;

  always @ (posedge clk) begin
    if (reset) begin
      reg_data <= 3'b0;
    end else if (load) begin
      reg_data <= load_data;
    end else begin
      reg_data <= {reg_data[1:0], reg_data[2]};
    end
  end

  assign serial_out = reg_data[0];

endmodule