module top_module (
  input clk,
  input reset, // Synchronous active-high reset
  input [7:0] d, // 8-bit input for the shift registers
  input select, // Select input to choose between the original and modified input value
  output reg [3:0] q // 4-bit output from the XOR operation module
);

  // Shift and OR operation module
  reg [7:0] shifted_value;
  always @ (posedge clk) begin
    if (reset) begin
      shifted_value <= 0;
    end else begin
      shifted_value <= {d[1:0], 4'b0} | 4'b1100;
    end
  end

  // 2-to-1 MUX module
  reg [7:0] mux_output;
  always @ (*) begin
    if (select) begin
      mux_output = shifted_value;
    end else begin
      mux_output = d;
    end
  end

  // Shift register module
  wire [3:0] shift_reg1_out;
  wire [3:0] shift_reg2_out;
  my_dff dff1 (.clk(clk), .reset(reset), .d(mux_output[3]), .q(shift_reg1_out[0]));
  my_dff dff2 (.clk(clk), .reset(reset), .d(mux_output[2]), .q(shift_reg1_out[1]));
  my_dff dff3 (.clk(clk), .reset(reset), .d(mux_output[1]), .q(shift_reg1_out[2]));
  my_dff dff4 (.clk(clk), .reset(reset), .d(mux_output[0]), .q(shift_reg1_out[3]));
  my_dff dff5 (.clk(clk), .reset(reset), .d(mux_output[7]), .q(shift_reg2_out[0]));
  my_dff dff6 (.clk(clk), .reset(reset), .d(mux_output[6]), .q(shift_reg2_out[1]));
  my_dff dff7 (.clk(clk), .reset(reset), .d(mux_output[5]), .q(shift_reg2_out[2]));
  my_dff dff8 (.clk(clk), .reset(reset), .d(mux_output[4]), .q(shift_reg2_out[3]));

  // XOR operation module
  always @ (*) begin
    q = shift_reg1_out ^ shift_reg2_out;
  end

endmodule

module my_dff (
  input clk,
  input reset,
  input d,
  output reg q
);
  always @ (posedge clk) begin
    if (reset) begin
      q <= 0;
    end else begin
      q <= d;
    end
  end
endmodule