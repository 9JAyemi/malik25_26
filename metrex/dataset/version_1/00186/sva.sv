// SVA for mig_7series_v1_9_ecc_merge_enc
module mig_7series_v1_9_ecc_merge_enc_sva #(
  parameter TCQ = 100,
  parameter PAYLOAD_WIDTH         = 64,
  parameter CODE_WIDTH            = 72,
  parameter DATA_BUF_ADDR_WIDTH   = 4,
  parameter DATA_BUF_OFFSET_WIDTH = 1,
  parameter DATA_WIDTH            = 64,
  parameter DQ_WIDTH              = 72,
  parameter ECC_WIDTH             = 8,
  parameter nCK_PER_CLK           = 4
)(
  input  logic                               clk,
  input  logic                               rst,
  input  logic [2*nCK_PER_CLK*PAYLOAD_WIDTH-1:0] wr_data,
  input  logic [2*nCK_PER_CLK*DATA_WIDTH/8-1:0]  wr_data_mask,
  input  logic [2*nCK_PER_CLK*DATA_WIDTH-1:0]     rd_merge_data,
  input  logic [CODE_WIDTH*ECC_WIDTH-1:0]         h_rows,
  input  logic [2*nCK_PER_CLK-1:0]                raw_not_ecc,
  input  logic [2*nCK_PER_CLK*DQ_WIDTH-1:0]       mc_wrdata,
  input  logic [2*nCK_PER_CLK*DQ_WIDTH/8-1:0]     mc_wrdata_mask
);

  // Static sanity
  initial begin
    assert (PAYLOAD_WIDTH <= DQ_WIDTH)
      else $error("PAYLOAD_WIDTH must be <= DQ_WIDTH");
    assert (CODE_WIDTH   <= DQ_WIDTH)
      else $error("CODE_WIDTH must be <= DQ_WIDTH");
    assert (DATA_WIDTH   <= PAYLOAD_WIDTH)
      else $error("DATA_WIDTH must be <= PAYLOAD_WIDTH");
  end

  function automatic logic [PAYLOAD_WIDTH-1:0] lane_merge(input int unsigned h);
    logic [PAYLOAD_WIDTH-1:0] m;
    int i;
    m = '0;
    for (i = 0; i < DATA_WIDTH/8; i++) begin
      m[i*8 +: 8] =
        wr_data_mask[h*DATA_WIDTH/8 + i]
          ? rd_merge_data[h*DATA_WIDTH + i*8 +: 8]
          : wr_data[h*PAYLOAD_WIDTH + i*8 +: 8];
    end
    if (PAYLOAD_WIDTH > DATA_WIDTH) begin
      m[PAYLOAD_WIDTH-1 -: (PAYLOAD_WIDTH-DATA_WIDTH)] =
        wr_data[(h+1)*PAYLOAD_WIDTH-1 -: (PAYLOAD_WIDTH-DATA_WIDTH)];
    end
    return m;
  endfunction

  function automatic logic [DQ_WIDTH-1:0] expected_word(
    input int unsigned j,
    input logic raw_mode
  );
    logic [PAYLOAD_WIDTH-1:0] m;
    logic [DQ_WIDTH-1:0] w;
    int k;
    m = lane_merge(j);
    w = '0;
    w = { {(DQ_WIDTH-PAYLOAD_WIDTH){1'b0}}, m };
    for (k = 0; k < ECC_WIDTH; k++) begin
      if (!raw_mode) begin
        w[CODE_WIDTH - k - 1] = ^(m[0 +: DATA_WIDTH] & h_rows[k*CODE_WIDTH +: DATA_WIDTH]);
      end
      // else leave as 0
    end
    return w;
  endfunction

  // mc_wrdata must match expected coding from current data and $past(raw_not_ecc)
  genvar j;
  generate
    for (j = 0; j < 2*nCK_PER_CLK; j++) begin : g_mc_check
      property p_mc_word;
        @(posedge clk) disable iff (rst)
          mc_wrdata[j*DQ_WIDTH +: DQ_WIDTH] == expected_word(j, $past(raw_not_ecc[j]));
      endproperty
      assert property (p_mc_word);

      // No X on output word
      assert property (@(posedge clk) disable iff (rst)
                       !$isunknown(mc_wrdata[j*DQ_WIDTH +: DQ_WIDTH]));

      // Coverage: raw/ECC modes seen
      cover property (@(posedge clk) disable iff (rst) $rose(raw_not_ecc[j]));
      cover property (@(posedge clk) disable iff (rst) $fell(raw_not_ecc[j]));

      // Coverage: all-0 and all-1 mask patterns for this lane
      cover property (@(posedge clk) disable iff (rst)
                      wr_data_mask[j*DATA_WIDTH/8 +: DATA_WIDTH/8] == {DATA_WIDTH/8{1'b0}});
      cover property (@(posedge clk) disable iff (rst)
                      wr_data_mask[j*DATA_WIDTH/8 +: DATA_WIDTH/8] == {DATA_WIDTH/8{1'b1}});

      // Coverage: at least one ECC bit evaluates to 1 in ECC mode
      genvar k;
      for (k = 0; k < ECC_WIDTH; k++) begin : g_cov_eccbit
        cover property (@(posedge clk) disable iff (rst)
                        !$past(raw_not_ecc[j]) &&
                        (^(lane_merge(j)[0 +: DATA_WIDTH] & h_rows[k*CODE_WIDTH +: DATA_WIDTH])));
      end
    end
  endgenerate

  // Output mask must be all-zero
  assert property (@(posedge clk) disable iff (rst)
                   mc_wrdata_mask == {2*nCK_PER_CLK*DQ_WIDTH/8{1'b0}});

  // No X on output mask
  assert property (@(posedge clk) disable iff (rst)
                   !$isunknown(mc_wrdata_mask));

endmodule

bind mig_7series_v1_9_ecc_merge_enc
  mig_7series_v1_9_ecc_merge_enc_sva #(
    .TCQ(TCQ),
    .PAYLOAD_WIDTH(PAYLOAD_WIDTH),
    .CODE_WIDTH(CODE_WIDTH),
    .DATA_BUF_ADDR_WIDTH(DATA_BUF_ADDR_WIDTH),
    .DATA_BUF_OFFSET_WIDTH(DATA_BUF_OFFSET_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DQ_WIDTH(DQ_WIDTH),
    .ECC_WIDTH(ECC_WIDTH),
    .nCK_PER_CLK(nCK_PER_CLK)
  ) sva_inst (
    .clk(clk),
    .rst(rst),
    .wr_data(wr_data),
    .wr_data_mask(wr_data_mask),
    .rd_merge_data(rd_merge_data),
    .h_rows(h_rows),
    .raw_not_ecc(raw_not_ecc),
    .mc_wrdata(mc_wrdata),
    .mc_wrdata_mask(mc_wrdata_mask)
  );