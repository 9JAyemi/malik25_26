module ad_datafmt #(
  parameter DATA_WIDTH = 16,
  parameter DISABLE = 0
) (
  input clk,
  input valid,
  input [(DATA_WIDTH-1):0] data,
  output valid_out,
  output [15:0] data_out,
  input dfmt_enable,
  input dfmt_type,
  input dfmt_se
);

  reg valid_int = 'd0;
  reg [15:0] data_int = 'd0;

  wire type_s;
  wire [15:0] data_out_s;

  generate
    if (DISABLE == 1) begin
      assign valid_out = valid;
      assign data_out = data;
    end else begin
      assign valid_out = valid_int;
      assign data_out = data_int;
    end
  endgenerate

  generate
    if (DATA_WIDTH < 16) begin
      wire signext_s;
      wire sign_s;

      assign signext_s = dfmt_enable & dfmt_se;
      assign sign_s = signext_s & (type_s ^ data[(DATA_WIDTH-1)]);
      assign data_out_s[15:DATA_WIDTH] = {(16-DATA_WIDTH){sign_s}};
    end
  endgenerate

  assign type_s = dfmt_enable & dfmt_type;
  assign data_out_s[(DATA_WIDTH-1)] = type_s ^ data[(DATA_WIDTH-1)];
  assign data_out_s[(DATA_WIDTH-2):0] = data[(DATA_WIDTH-2):0];

  always @(posedge clk) begin
    valid_int <= valid;
    data_int <= data_out_s[15:0];
  end

endmodule