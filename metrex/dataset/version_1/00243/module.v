
module DDC (
  input clk,
  input reset,
  input [15:0] data_in,
  input [31:0] freq,
  input [7:0] dec_factor,
  output reg [15:0] data_out,
  output [31:0] out_freq
);

  // Internal signals
  reg [15:0] filtered_data;
  reg [31:0] counter;

  // Low-pass filter
  always @(posedge clk) begin
    if (reset) begin
      filtered_data <= 16'h0;
    end else begin
      filtered_data <= (data_in + filtered_data) >> 1;
    end
  end

  // Down-sampling
  always @(posedge clk) begin
    if (reset) begin
      counter <= 32'h0;
      data_out <= 16'h0;
    end else begin
      counter <= counter + 1;
      if (counter == dec_factor - 1) begin
        counter <= 32'h0;
        data_out <= filtered_data;
      end
    end
  end

  // Output frequency
  assign out_freq = freq / dec_factor;

endmodule
module DUC (
  input clk,
  input reset,
  input [15:0] data_in,
  input [31:0] freq,
  input [7:0] interp_factor,
  output reg [15:0] data_out,
  output [31:0] out_freq
);

  // Internal signals
  reg [15:0] upsampled_data;
  reg [31:0] counter;

  // Up-sampling
  always @(posedge clk) begin
    if (reset) begin
      counter <= 32'h0;
      upsampled_data <= 16'h0;
    end else begin
      counter <= counter + 1;
      if (counter == interp_factor - 1) begin
        counter <= 32'h0;
        upsampled_data <= data_in;
      end else begin
        upsampled_data <= 16'h0;
      end
    end
  end

  // Digital filter
  always @(posedge clk) begin
    if (reset) begin
      data_out <= 16'h0;
    end else begin
      data_out <= (upsampled_data + data_out) >> 1;
    end
  end

  // Output frequency
  assign out_freq = freq * interp_factor;

endmodule