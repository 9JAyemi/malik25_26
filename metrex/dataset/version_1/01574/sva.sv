// SVA for axi_hdmi_tx_es
// Bind-in assertions only; no DUT changes required.

module axi_hdmi_tx_es_sva #(parameter int DATA_WIDTH = 32) (
  input logic                          hdmi_clk,
  input logic                          hdmi_hs_de,
  input logic                          hdmi_vs_de,
  input logic [DATA_WIDTH-1:0]         hdmi_data_de,
  input logic [DATA_WIDTH-1:0]         hdmi_data,

  // Internal DUT signals (bound hierarchically)
  input logic                          hdmi_hs_de_d,
  input logic                          hdmi_hs_de_2d,
  input logic                          hdmi_hs_de_3d,
  input logic                          hdmi_hs_de_4d,
  input logic                          hdmi_hs_de_5d,

  input logic [DATA_WIDTH-1:0]         hdmi_data_d,
  input logic [DATA_WIDTH-1:0]         hdmi_data_2d,
  input logic [DATA_WIDTH-1:0]         hdmi_data_3d,
  input logic [DATA_WIDTH-1:0]         hdmi_data_4d,
  input logic [DATA_WIDTH-1:0]         hdmi_data_5d,

  input logic [DATA_WIDTH-1:0]         hdmi_sav_s,
  input logic [DATA_WIDTH-1:0]         hdmi_eav_s
);

  localparam int BYTE_WIDTH = DATA_WIDTH/8;

  // Static param check
  initial assert (DATA_WIDTH%8==0)
    else $error("axi_hdmi_tx_es: DATA_WIDTH must be a multiple of 8");

  // Past-valid guard (no reset provided in DUT)
  logic past_valid;
  always_ff @(posedge hdmi_clk) past_valid <= 1'b1;

  // Constant vectors
  localparam logic [DATA_WIDTH-1:0] ALL0 = {BYTE_WIDTH{8'h00}};
  localparam logic [DATA_WIDTH-1:0] ALLF = {BYTE_WIDTH{8'hff}};
  localparam logic [DATA_WIDTH-1:0] SAV_VS1 = {BYTE_WIDTH{8'h80}};
  localparam logic [DATA_WIDTH-1:0] SAV_VS0 = {BYTE_WIDTH{8'hab}};
  localparam logic [DATA_WIDTH-1:0] EAV_VS1 = {BYTE_WIDTH{8'h9d}};
  localparam logic [DATA_WIDTH-1:0] EAV_VS0 = {BYTE_WIDTH{8'hb6}};

  // Combinational sav/eav generation correctness
  assert property (@(posedge hdmi_clk) hdmi_vs_de |-> (hdmi_sav_s==SAV_VS1 && hdmi_eav_s==EAV_VS1));
  assert property (@(posedge hdmi_clk) !hdmi_vs_de |-> (hdmi_sav_s==SAV_VS0 && hdmi_eav_s==EAV_VS0));

  // Delay-chain integrity
  assert property (@(posedge hdmi_clk) disable iff (!past_valid)
    hdmi_hs_de_d  == $past(hdmi_hs_de)     &&
    hdmi_hs_de_2d == $past(hdmi_hs_de_d)   &&
    hdmi_hs_de_3d == $past(hdmi_hs_de_2d)  &&
    hdmi_hs_de_4d == $past(hdmi_hs_de_3d)  &&
    hdmi_hs_de_5d == $past(hdmi_hs_de_4d));

  assert property (@(posedge hdmi_clk) disable iff (!past_valid)
    hdmi_data_2d == $past(hdmi_data_d)   &&
    hdmi_data_3d == $past(hdmi_data_2d) &&
    hdmi_data_4d == $past(hdmi_data_3d) &&
    hdmi_data_5d == $past(hdmi_data_4d));

  // First case-tree (hdmi_data_d next-cycle result)
  // Patterns on {$past(hs_4d,hs_3d,hs_2d,hs_d,hs)}
  assert property (@(posedge hdmi_clk) disable iff (!past_valid)
    ({$past(hdmi_hs_de_4d),$past(hdmi_hs_de_3d),$past(hdmi_hs_de_2d),$past(hdmi_hs_de_d),$past(hdmi_hs_de)}==5'b11000)
    |-> (hdmi_data_d==ALL0));

  assert property (@(posedge hdmi_clk) disable iff (!past_valid)
    ({$past(hdmi_hs_de_4d),$past(hdmi_hs_de_3d),$past(hdmi_hs_de_2d),$past(hdmi_hs_de_d),$past(hdmi_hs_de)}==5'b11100)
    |-> (hdmi_data_d==ALL0));

  assert property (@(posedge hdmi_clk) disable iff (!past_valid)
    ({$past(hdmi_hs_de_4d),$past(hdmi_hs_de_3d),$past(hdmi_hs_de_2d),$past(hdmi_hs_de_d),$past(hdmi_hs_de)}==5'b11110)
    |-> (hdmi_data_d==ALLF));

  assert property (@(posedge hdmi_clk) disable iff (!past_valid)
    ({$past(hdmi_hs_de_4d),$past(hdmi_hs_de_3d),$past(hdmi_hs_de_2d),$past(hdmi_hs_de_d),$past(hdmi_hs_de)}==5'b10000)
    |-> (hdmi_data_d==$past(hdmi_eav_s)));

  assert property (@(posedge hdmi_clk) disable iff (!past_valid)
    !({$past(hdmi_hs_de_4d),$past(hdmi_hs_de_3d),$past(hdmi_hs_de_2d),$past(hdmi_hs_de_d),$past(hdmi_hs_de)} inside
      {5'b11000,5'b11100,5'b11110,5'b10000})
    |-> (hdmi_data_d==$past(hdmi_data_de)));

  // Second case-tree (final hdmi_data next-cycle result)
  // Patterns on {$past(hs_5d,hs_4d,hs_3d,hs_2d,hs_d)}
  assert property (@(posedge hdmi_clk) disable iff (!past_valid)
    ({$past(hdmi_hs_de_5d),$past(hdmi_hs_de_4d),$past(hdmi_hs_de_3d),$past(hdmi_hs_de_2d),$past(hdmi_hs_de_d)}==5'b00111)
    |-> (hdmi_data==ALL0));

  assert property (@(posedge hdmi_clk) disable iff (!past_valid)
    ({$past(hdmi_hs_de_5d),$past(hdmi_hs_de_4d),$past(hdmi_hs_de_3d),$past(hdmi_hs_de_2d),$past(hdmi_hs_de_d)}==5'b00011)
    |-> (hdmi_data==ALL0));

  assert property (@(posedge hdmi_clk) disable iff (!past_valid)
    ({$past(hdmi_hs_de_5d),$past(hdmi_hs_de_4d),$past(hdmi_hs_de_3d),$past(hdmi_hs_de_2d),$past(hdmi_hs_de_d)}==5'b00001)
    |-> (hdmi_data==ALLF));

  assert property (@(posedge hdmi_clk) disable iff (!past_valid)
    ({$past(hdmi_hs_de_5d),$past(hdmi_hs_de_4d),$past(hdmi_hs_de_3d),$past(hdmi_hs_de_2d),$past(hdmi_hs_de_d)}==5'b01111)
    |-> (hdmi_data==$past(hdmi_sav_s)));

  assert property (@(posedge hdmi_clk) disable iff (!past_valid)
    !({$past(hdmi_hs_de_5d),$past(hdmi_hs_de_4d),$past(hdmi_hs_de_3d),$past(hdmi_hs_de_2d),$past(hdmi_hs_de_d)} inside
      {5'b00111,5'b00011,5'b00001,5'b01111})
    |-> (hdmi_data==$past(hdmi_data_5d)));

  // Targeted coverage
  // First case patterns
  cover property (@(posedge hdmi_clk) ({hdmi_hs_de_4d,hdmi_hs_de_3d,hdmi_hs_de_2d,hdmi_hs_de_d,hdmi_hs_de}==5'b11000));
  cover property (@(posedge hdmi_clk) ({hdmi_hs_de_4d,hdmi_hs_de_3d,hdmi_hs_de_2d,hdmi_hs_de_d,hdmi_hs_de}==5'b11100));
  cover property (@(posedge hdmi_clk) ({hdmi_hs_de_4d,hdmi_hs_de_3d,hdmi_hs_de_2d,hdmi_hs_de_d,hdmi_hs_de}==5'b11110));
  cover property (@(posedge hdmi_clk) ({hdmi_hs_de_4d,hdmi_hs_de_3d,hdmi_hs_de_2d,hdmi_hs_de_d,hdmi_hs_de}==5'b10000));

  // Second case patterns
  cover property (@(posedge hdmi_clk) ({hdmi_hs_de_5d,hdmi_hs_de_4d,hdmi_hs_de_3d,hdmi_hs_de_2d,hdmi_hs_de_d}==5'b00111));
  cover property (@(posedge hdmi_clk) ({hdmi_hs_de_5d,hdmi_hs_de_4d,hdmi_hs_de_3d,hdmi_hs_de_2d,hdmi_hs_de_d}==5'b00011));
  cover property (@(posedge hdmi_clk) ({hdmi_hs_de_5d,hdmi_hs_de_4d,hdmi_hs_de_3d,hdmi_hs_de_2d,hdmi_hs_de_d}==5'b00001));
  cover property (@(posedge hdmi_clk) ({hdmi_hs_de_5d,hdmi_hs_de_4d,hdmi_hs_de_3d,hdmi_hs_de_2d,hdmi_hs_de_d}==5'b01111));

  // VS polarity coverage
  cover property (@(posedge hdmi_clk) $rose(hdmi_vs_de));
  cover property (@(posedge hdmi_clk) $fell(hdmi_vs_de));

  // SAV/EAV end-to-end value coverage
  cover property (@(posedge hdmi_clk) disable iff (!past_valid)
    ({$past(hdmi_hs_de_5d),$past(hdmi_hs_de_4d),$past(hdmi_hs_de_3d),$past(hdmi_hs_de_2d),$past(hdmi_hs_de_d)}==5'b01111 && $past(hdmi_vs_de))
    |-> (hdmi_data==SAV_VS1));
  cover property (@(posedge hdmi_clk) disable iff (!past_valid)
    ({$past(hdmi_hs_de_5d),$past(hdmi_hs_de_4d),$past(hdmi_hs_de_3d),$past(hdmi_hs_de_2d),$past(hdmi_hs_de_d)}==5'b01111 && !$past(hdmi_vs_de))
    |-> (hdmi_data==SAV_VS0));

  cover property (@(posedge hdmi_clk) disable iff (!past_valid)
    ({$past(hdmi_hs_de_4d),$past(hdmi_hs_de_3d),$past(hdmi_hs_de_2d),$past(hdmi_hs_de_d),$past(hdmi_hs_de)}==5'b10000 && $past(hdmi_vs_de))
    |-> (hdmi_data_d==EAV_VS1));
  cover property (@(posedge hdmi_clk) disable iff (!past_valid)
    ({$past(hdmi_hs_de_4d),$past(hdmi_hs_de_3d),$past(hdmi_hs_de_2d),$past(hdmi_hs_de_d),$past(hdmi_hs_de)}==5'b10000 && !$past(hdmi_vs_de))
    |-> (hdmi_data_d==EAV_VS0));

endmodule

// Bind into DUT
bind axi_hdmi_tx_es axi_hdmi_tx_es_sva #(.DATA_WIDTH(DATA_WIDTH)) axi_hdmi_tx_es_sva_i (
  .hdmi_clk(hdmi_clk),
  .hdmi_hs_de(hdmi_hs_de),
  .hdmi_vs_de(hdmi_vs_de),
  .hdmi_data_de(hdmi_data_de),
  .hdmi_data(hdmi_data),

  .hdmi_hs_de_d(hdmi_hs_de_d),
  .hdmi_hs_de_2d(hdmi_hs_de_2d),
  .hdmi_hs_de_3d(hdmi_hs_de_3d),
  .hdmi_hs_de_4d(hdmi_hs_de_4d),
  .hdmi_hs_de_5d(hdmi_hs_de_5d),

  .hdmi_data_d(hdmi_data_d),
  .hdmi_data_2d(hdmi_data_2d),
  .hdmi_data_3d(hdmi_data_3d),
  .hdmi_data_4d(hdmi_data_4d),
  .hdmi_data_5d(hdmi_data_5d),

  .hdmi_sav_s(hdmi_sav_s),
  .hdmi_eav_s(hdmi_eav_s)
);