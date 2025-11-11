
module dc_filter (
  // data interface
  input clk,
  input valid,
  input [15:0] data,
  output reg valid_out,
  output reg [15:0] data_out,
  // control interface
  input dcfilt_enb,
  input [15:0] dcfilt_coeff,
  input [15:0] dcfilt_offset
);
  // internal registers
  reg [47:0] dc_offset;
  reg [47:0] dc_offset_d;
  reg valid_d;
  reg [15:0] data_d;
  reg valid_2d;
  reg [15:0] data_2d;
  reg [15:0] data_dcfilt;
  // internal signals
  wire [47:0] dc_offset_s = dc_offset[32:0] - (dc_offset[47:33] << 15);
  // cancelling the dc offset
  always @(posedge clk) begin
    dc_offset_d <= dc_offset_s;
    valid_d <= valid;
    if (valid == 1'b1) begin
      data_d <= data + dcfilt_offset;
    end
    valid_2d <= valid_d;
    data_2d <= data_d;
    data_dcfilt <= data_d - dc_offset_s[32:17];
    if (dcfilt_enb == 1'b1) begin
      valid_out <= valid_2d;
      data_out <= data_dcfilt;
    end else begin
      valid_out <= valid_2d;
      data_out <= data_2d;
    end
  end
  // always block to avoid latch
  always @(posedge clk) begin
    dc_offset <= dc_offset_d;
  end
endmodule