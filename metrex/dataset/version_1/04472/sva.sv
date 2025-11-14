// SVA for mig_7series_v4_0_ecc_merge_enc
// Bindable, concise, and checks merge, ECC placement/parity, masks, and timing.

`ifndef ECC_MERGE_ENC_SVA_SV
`define ECC_MERGE_ENC_SVA_SV

module ecc_merge_enc_sva #(
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
  input  logic                                clk,
  input  logic                                rst,
  input  logic [2*nCK_PER_CLK*PAYLOAD_WIDTH-1:0] wr_data,
  input  logic [2*nCK_PER_CLK*DATA_WIDTH/8-1:0]  wr_data_mask,
  input  logic [2*nCK_PER_CLK*DATA_WIDTH-1:0]    rd_merge_data,
  input  logic [CODE_WIDTH*ECC_WIDTH-1:0]        h_rows,
  input  logic [2*nCK_PER_CLK-1:0]               raw_not_ecc,
  input  logic [2*nCK_PER_CLK*DQ_WIDTH-1:0]      mc_wrdata,
  input  logic [2*nCK_PER_CLK*DQ_WIDTH/8-1:0]    mc_wrdata_mask
);

  // Clocking
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // mc_wrdata_mask is always zero
  assert property (1'b1 |=> mc_wrdata_mask == '0)
    else $error("mc_wrdata_mask must be all zeros");

  // Payload merge: each byte selects rd_merge_data when masked, else wr_data
  genvar j,i;
  generate
    for (j=0; j<2*nCK_PER_CLK; j++) begin: g_merge_chk_lane
      for (i=0; i<DATA_WIDTH/8; i++) begin: g_merge_chk_byte
        assert property (
          1'b1 |=> mc_wrdata[j*DQ_WIDTH + i*8 +: 8] ==
                    ($past(wr_data_mask[j*DATA_WIDTH/8+i])
                       ? $past(rd_merge_data[j*DATA_WIDTH + i*8 +: 8])
                       : $past(wr_data     [j*PAYLOAD_WIDTH + i*8 +: 8]))
        ) else $error("Merged byte mismatch at lane %0d byte %0d", j, i);
      end

      if (PAYLOAD_WIDTH > DATA_WIDTH) begin: g_merge_hi_chk
        localparam int HIW = PAYLOAD_WIDTH - DATA_WIDTH;
        // High payload bits (above DATA_WIDTH) pass-through from wr_data
        assert property (
          1'b1 |=> mc_wrdata[j*DQ_WIDTH + DATA_WIDTH +: HIW] ==
                    $past(wr_data[(j+1)*PAYLOAD_WIDTH-1 -: HIW])
        ) else $error("High payload bits mismatch at lane %0d", j);
      end
    end
  endgenerate

  // Payload placement: full PAYLOAD slice must equal merged result (compositional check)
  // Lower PAYLOAD bits of each DQ word equal the merged payload already checked per byte.

  // ECC bits placement and parity
  // If ECC enabled (~raw_not_ecc), top ECC bits equal parity of DATA_WIDTH LSBs of payload against h_rows row k.
  // If ECC disabled (raw_not_ecc), ECC bits are 0.
  genvar k;
  generate
    for (j=0; j<2*nCK_PER_CLK; j++) begin: g_ecc_lane
      for (k=0; k<ECC_WIDTH; k++) begin: g_ecc_bit
        // Disabled: ECC bits must be 0
        assert property (
          $past(raw_not_ecc[j]) |-> (mc_wrdata[j*DQ_WIDTH + (CODE_WIDTH - k - 1)] == 1'b0)
        ) else $error("ECC bit not zero in raw mode at lane %0d bit %0d", j, k);

        // Enabled: ECC bit equals parity of merged DATA_WIDTH bits AND h_rows row
        assert property (
          !$past(raw_not_ecc[j]) |-> (
            mc_wrdata[j*DQ_WIDTH + (CODE_WIDTH - k - 1)] ==
              ^( mc_wrdata[j*DQ_WIDTH +: DATA_WIDTH] & $past(h_rows[k*CODE_WIDTH +: DATA_WIDTH]) )
          )
        ) else $error("ECC parity mismatch at lane %0d bit %0d", j, k);
      end
    end
  endgenerate

  // Optional: any bits above CODE_WIDTH (if any exist) must be zero
  if (DQ_WIDTH > CODE_WIDTH) begin : g_above_code_zero
    localparam int EXTRA = DQ_WIDTH - CODE_WIDTH;
    genvar jj;
    for (jj=0; jj<2*nCK_PER_CLK; jj++) begin : g_above_lane
      assert property (1'b1 |=> mc_wrdata[(jj+1)*DQ_WIDTH-1 -: EXTRA] == '0)
        else $error("Bits above CODE_WIDTH non-zero at lane %0d", jj);
    end
  end

  // Simple timing sanity: registered output updates one cycle after inputs are sampled
  // (already enforced by |=> in checks above)

  // Coverage: see both ECC modes, masked and unmasked bytes, and at least one ECC parity=1
  // ECC modes
  for (j=0; j<2*nCK_PER_CLK; j++) begin: g_cov_modes
    cover property ($past(raw_not_ecc[j]) && !$isunknown($past(raw_not_ecc[j])));
    cover property (!$past(raw_not_ecc[j]) && !$isunknown($past(raw_not_ecc[j])));
  end

  // Masked and unmasked bytes observed
  for (j=0; j<2*nCK_PER_CLK; j++) begin: g_cov_mask
    cover property (|$past(wr_data_mask[j*DATA_WIDTH/8 +: DATA_WIDTH/8]));
    cover property (~|$past(wr_data_mask[j*DATA_WIDTH/8 +: DATA_WIDTH/8]));
  end

  // ECC parity toggles to 1 at least once
  for (j=0; j<2*nCK_PER_CLK; j++) begin: g_cov_parity
    for (k=0; k<ECC_WIDTH; k++) begin: g_cov_bit
      cover property (
        !$past(raw_not_ecc[j]) && ^(mc_wrdata[j*DQ_WIDTH +: DATA_WIDTH] & $past(h_rows[k*CODE_WIDTH +: DATA_WIDTH]))
      );
    end
  end

endmodule

// Bind into DUT
bind mig_7series_v4_0_ecc_merge_enc ecc_merge_enc_sva #(
  .TCQ(TCQ),
  .PAYLOAD_WIDTH(PAYLOAD_WIDTH),
  .CODE_WIDTH(CODE_WIDTH),
  .DATA_BUF_ADDR_WIDTH(DATA_BUF_ADDR_WIDTH),
  .DATA_BUF_OFFSET_WIDTH(DATA_BUF_OFFSET_WIDTH),
  .DATA_WIDTH(DATA_WIDTH),
  .DQ_WIDTH(DQ_WIDTH),
  .ECC_WIDTH(ECC_WIDTH),
  .nCK_PER_CLK(nCK_PER_CLK)
) u_ecc_merge_enc_sva (
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

`endif