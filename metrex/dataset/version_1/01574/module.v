

module axi_hdmi_tx_es #(

  parameter   DATA_WIDTH = 32) (

  input                   hdmi_clk,
  input                   hdmi_hs_de,
  input                   hdmi_vs_de,
  input       [(DATA_WIDTH-1):0]  hdmi_data_de,
  output  reg [(DATA_WIDTH-1):0]  hdmi_data);

  localparam  BYTE_WIDTH = DATA_WIDTH/8;

  reg                         hdmi_hs_de_d = 'd0;
  reg     [(DATA_WIDTH-1):0]  hdmi_data_d = 'd0;
  reg                         hdmi_hs_de_2d = 'd0;
  reg     [(DATA_WIDTH-1):0]  hdmi_data_2d = 'd0;
  reg                         hdmi_hs_de_3d = 'd0;
  reg     [(DATA_WIDTH-1):0]  hdmi_data_3d = 'd0;
  reg                         hdmi_hs_de_4d = 'd0;
  reg     [(DATA_WIDTH-1):0]  hdmi_data_4d = 'd0;
  reg                         hdmi_hs_de_5d = 'd0;
  reg     [(DATA_WIDTH-1):0]  hdmi_data_5d = 'd0;

  wire    [(DATA_WIDTH-1):0]  hdmi_sav_s;
  wire    [(DATA_WIDTH-1):0]  hdmi_eav_s;

  assign hdmi_sav_s = (hdmi_vs_de == 1) ? {BYTE_WIDTH{8'h80}} : {BYTE_WIDTH{8'hab}};
  assign hdmi_eav_s = (hdmi_vs_de == 1) ? {BYTE_WIDTH{8'h9d}} : {BYTE_WIDTH{8'hb6}};

  always @(posedge hdmi_clk) begin
    hdmi_hs_de_d <= hdmi_hs_de;
    case ({hdmi_hs_de_4d, hdmi_hs_de_3d, hdmi_hs_de_2d,
      hdmi_hs_de_d, hdmi_hs_de})
      5'b11000: hdmi_data_d <= {BYTE_WIDTH{8'h00}};
      5'b11100: hdmi_data_d <= {BYTE_WIDTH{8'h00}};
      5'b11110: hdmi_data_d <= {BYTE_WIDTH{8'hff}};
      5'b10000: hdmi_data_d <= hdmi_eav_s;
      default: hdmi_data_d <= hdmi_data_de;
    endcase
    hdmi_hs_de_2d <= hdmi_hs_de_d;
    hdmi_data_2d <= hdmi_data_d;
    hdmi_hs_de_3d <= hdmi_hs_de_2d;
    hdmi_data_3d <= hdmi_data_2d;
    hdmi_hs_de_4d <= hdmi_hs_de_3d;
    hdmi_data_4d <= hdmi_data_3d;
    hdmi_hs_de_5d <= hdmi_hs_de_4d;
    hdmi_data_5d <= hdmi_data_4d;
    case ({hdmi_hs_de_5d, hdmi_hs_de_4d, hdmi_hs_de_3d,
      hdmi_hs_de_2d, hdmi_hs_de_d})
      5'b00111: hdmi_data <= {BYTE_WIDTH{8'h00}};
      5'b00011: hdmi_data <= {BYTE_WIDTH{8'h00}};
      5'b00001: hdmi_data <= {BYTE_WIDTH{8'hff}};
      5'b01111: hdmi_data <= hdmi_sav_s;
      default:  hdmi_data <= hdmi_data_5d;
    endcase
  end

endmodule

