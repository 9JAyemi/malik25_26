// SVA for xgmii_baser_enc_64
// Bind-in module; concise but checks reset, pipeline latency, functional mapping, X-safety, and key coverage.

module xgmii_baser_enc_64_sva #(
  parameter DATA_WIDTH = 64,
  parameter CTRL_WIDTH = (DATA_WIDTH/8),
  parameter HDR_WIDTH  = 2
)(
  input                        clk,
  input                        rst,
  input  [DATA_WIDTH-1:0]      xgmii_txd,
  input  [CTRL_WIDTH-1:0]      xgmii_txc,
  input  [DATA_WIDTH-1:0]      encoded_tx_data,
  input  [HDR_WIDTH-1:0]       encoded_tx_hdr,
  input  [DATA_WIDTH-1:0]      data_reg,
  input  [HDR_WIDTH-1:0]       header_reg
);
  default clocking cb @(posedge clk); endclocking

  // Warm-up to make $past safe on first cycle
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Static width sanity (flags the off-by-one/truncation issue if present)
  localparam int RHS_W = $bits({xgmii_txd[DATA_WIDTH-1-CTRL_WIDTH:0], xgmii_txc});
  initial assert (RHS_W == DATA_WIDTH)
    else $error("Width mismatch: concat width %0d != DATA_WIDTH %0d", RHS_W, DATA_WIDTH);

  // Reset: outputs go to zero exactly one cycle after rst is seen
  assert property (disable iff (!past_valid)
    rst |=> (encoded_tx_data == '0 && encoded_tx_hdr == '0));

  // Pipeline stage checks (outputs are 1-cycle copies of internal regs)
  assert property (disable iff (!past_valid)
    encoded_tx_data == $past(data_reg));
  assert property (disable iff (!past_valid)
    encoded_tx_hdr  == $past(header_reg));

  // Functional mapping through the pipeline (including reset effect)
  // Note: effective concatenation is {xgmii_txd[DATA_WIDTH-CTRL_WIDTH-1:0], xgmii_txc}
  assert property (disable iff (!past_valid)
    encoded_tx_data == $past(rst ? '0 : {xgmii_txd[DATA_WIDTH-CTRL_WIDTH-1:0], xgmii_txc}));
  assert property (disable iff (!past_valid)
    encoded_tx_hdr  == $past(rst ? '0 : {xgmii_txd[DATA_WIDTH-2], xgmii_txd[DATA_WIDTH-1]}));

  // No X/Z on outputs when not in reset
  assert property (disable iff (rst || !past_valid)
    !$isunknown({encoded_tx_data, encoded_tx_hdr}));

  // Coverage: exercise TXC influence and all header encodings
  cover property (disable iff (rst || !past_valid)
    encoded_tx_data[CTRL_WIDTH-1:0] != '0); // non-zero control nibble observed
  cover property (disable iff (rst || !past_valid) encoded_tx_hdr == 2'b00);
  cover property (disable iff (rst || !past_valid) encoded_tx_hdr == 2'b01);
  cover property (disable iff (rst || !past_valid) encoded_tx_hdr == 2'b10);
  cover property (disable iff (rst || !past_valid) encoded_tx_hdr == 2'b11);

endmodule

bind xgmii_baser_enc_64 xgmii_baser_enc_64_sva #(
  .DATA_WIDTH(DATA_WIDTH),
  .CTRL_WIDTH(CTRL_WIDTH),
  .HDR_WIDTH (HDR_WIDTH)
) sva (.*);