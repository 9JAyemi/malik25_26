// SVA for mig_7series_v2_0_ecc_merge_enc
// Bindable, concise, full functional checks and key coverage

module mig_7series_v2_0_ecc_merge_enc_sva #(
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
  input  logic clk,
  input  logic rst,

  input  logic [2*nCK_PER_CLK*PAYLOAD_WIDTH-1:0] wr_data,
  input  logic [2*nCK_PER_CLK*DATA_WIDTH/8-1:0]  wr_data_mask,
  input  logic [2*nCK_PER_CLK*DATA_WIDTH-1:0]    rd_merge_data,

  input  logic [2*nCK_PER_CLK*PAYLOAD_WIDTH-1:0] wr_data_r,
  input  logic [2*nCK_PER_CLK*DATA_WIDTH/8-1:0]  wr_data_mask_r,
  input  logic [2*nCK_PER_CLK*DATA_WIDTH-1:0]    rd_merge_data_r,

  input  logic [CODE_WIDTH*ECC_WIDTH-1:0]        h_rows,
  input  logic [2*nCK_PER_CLK-1:0]               raw_not_ecc,
  input  logic [2*nCK_PER_CLK-1:0]               raw_not_ecc_r,

  input  logic [2*nCK_PER_CLK*DQ_WIDTH-1:0]      mc_wrdata,
  input  logic [2*nCK_PER_CLK*DQ_WIDTH/8-1:0]    mc_wrdata_mask
);
  localparam int BEATS = 2*nCK_PER_CLK;
  localparam int BYTES = DATA_WIDTH/8;

  // Pipeline checks
  p_wdata_r:       assert property (@(posedge clk) disable iff (rst) wr_data_r       == $past(wr_data));
  p_wmask_r:       assert property (@(posedge clk) disable iff (rst) wr_data_mask_r  == $past(wr_data_mask));
  p_rdmerge_r:     assert property (@(posedge clk) disable iff (rst) rd_merge_data_r == $past(rd_merge_data));
  p_raw_r:         assert property (@(posedge clk) disable iff (rst) raw_not_ecc_r   == $past(raw_not_ecc));

  // Output mask is constant zero
  p_mask_zero:     assert property (@(posedge clk) ##0 mc_wrdata_mask == {2*nCK_PER_CLK*DQ_WIDTH/8{1'b0}});

  genvar j,i,ek;
  generate
    for (j=0; j<BEATS; j=j+1) begin : GEN_BEAT
      // Expected merged payload data for this beat
      wire [PAYLOAD_WIDTH-1:0] exp_pay;
      for (i=0; i<BYTES; i=i+1) begin : GEN_BYTE
        assign exp_pay[i*8 +: 8] =
          wr_data_mask[j*BYTES+i]
            ? rd_merge_data[j*DATA_WIDTH + i*8 +: 8]
            : wr_data     [j*PAYLOAD_WIDTH + i*8 +: 8];
      end
      if (PAYLOAD_WIDTH > DATA_WIDTH) begin : GEN_PAD
        assign exp_pay[PAYLOAD_WIDTH-1 -: (PAYLOAD_WIDTH-DATA_WIDTH)] =
               wr_data[(j+1)*PAYLOAD_WIDTH-1 -: (PAYLOAD_WIDTH-DATA_WIDTH)];
      end

      // Payload must land exactly
      a_payload: assert property (@(posedge clk) disable iff (rst)
                                  ##0 mc_wrdata[j*DQ_WIDTH +: PAYLOAD_WIDTH] == exp_pay);

      // Zero regions above CODE_WIDTH (never touched)
      if (DQ_WIDTH > CODE_WIDTH) begin : GEN_ZABV
        a_zero_above_code: assert property (@(posedge clk) disable iff (rst)
                                  ##0 mc_wrdata[j*DQ_WIDTH+CODE_WIDTH +: (DQ_WIDTH-CODE_WIDTH)]
                                      == {(DQ_WIDTH-CODE_WIDTH){1'b0}});
      end
      // Zero region between payload and ECC field bottom
      if (CODE_WIDTH > (PAYLOAD_WIDTH + ECC_WIDTH)) begin : GEN_ZMID
        localparam int MIDW = CODE_WIDTH - PAYLOAD_WIDTH - ECC_WIDTH;
        a_zero_mid: assert property (@(posedge clk) disable iff (rst)
                                  ##0 mc_wrdata[j*DQ_WIDTH+PAYLOAD_WIDTH +: MIDW] == {MIDW{1'b0}});
      end

      // ECC bits placement and value (or zero in RAW mode)
      for (ek=0; ek<ECC_WIDTH; ek=ek+1) begin : GEN_ECC
        wire exp_ecc_bit = ^(exp_pay[0 +: DATA_WIDTH] & h_rows[ek*CODE_WIDTH +: DATA_WIDTH]);
        a_ecc_bit: assert property (@(posedge clk) disable iff (rst)
                              ##0 ( raw_not_ecc_r[j]
                                   ? (mc_wrdata[j*DQ_WIDTH + CODE_WIDTH - ek - 1] == 1'b0)
                                   : (mc_wrdata[j*DQ_WIDTH + CODE_WIDTH - ek - 1] == exp_ecc_bit)));
      end
    end
  endgenerate

  // Basic X-check on key outputs after update
  p_no_x_out: assert property (@(posedge clk) disable iff (rst) ##0 !$isunknown(mc_wrdata));

  // Coverage
  // Observe both RAW and ECC modes
  cover_raw_mode: cover property (@(posedge clk) !rst ##1 (|raw_not_ecc_r));
  cover_ecc_mode: cover property (@(posedge clk) !rst ##1 (~|raw_not_ecc_r == 1'b1));
  // Mask extremes on any beat
  cover_mask_all0: cover property (@(posedge clk) !rst ##1 (wr_data_mask == {BEATS*BYTES{1'b0}}));
  cover_mask_all1: cover property (@(posedge clk) !rst ##1 (wr_data_mask == {BEATS*BYTES{1'b1}}));
  // ECC bit can be 1 in ECC mode (check ek=0 for conciseness)
  cover_ecc1: cover property (@(posedge clk) !rst ##0 (|{genvar'(0)}), 1'b1); // placeholder to ensure legal syntax
  // Practical concise ECC-1 cover (uses beat 0, bit 0)
  wire [PAYLOAD_WIDTH-1:0] exp_pay_cg = (PAYLOAD_WIDTH>0) ? {PAYLOAD_WIDTH{1'b0}} : '0; // dummy init to please tools
  // Simple ECC-1 cover using beat 0, recompute locally
  if (BEATS>0) begin
    wire [PAYLOAD_WIDTH-1:0] exp_pay0;
    for (i=0; i<BYTES; i=i+1) begin : CG_BYTE
      assign exp_pay0[i*8 +: 8] =
        wr_data_mask[i] ? rd_merge_data[i*8 +: 8] : wr_data[i*8 +: 8];
    end
    if (PAYLOAD_WIDTH > DATA_WIDTH) begin : CG_PAD
      assign exp_pay0[PAYLOAD_WIDTH-1 -: (PAYLOAD_WIDTH-DATA_WIDTH)] =
             wr_data[PAYLOAD_WIDTH-1 -: (PAYLOAD_WIDTH-DATA_WIDTH)];
    end
    wire ecc0 = ^(exp_pay0[0 +: DATA_WIDTH] & h_rows[0*CODE_WIDTH +: DATA_WIDTH]);
    cover_ecc_one: cover property (@(posedge clk) !rst ##0 (!raw_not_ecc_r[0] && ecc0));
  end

endmodule

// Bind into DUT
bind mig_7series_v2_0_ecc_merge_enc
  mig_7series_v2_0_ecc_merge_enc_sva #(
    .TCQ(TCQ),
    .PAYLOAD_WIDTH(PAYLOAD_WIDTH),
    .CODE_WIDTH(CODE_WIDTH),
    .DATA_BUF_ADDR_WIDTH(DATA_BUF_ADDR_WIDTH),
    .DATA_BUF_OFFSET_WIDTH(DATA_BUF_OFFSET_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DQ_WIDTH(DQ_WIDTH),
    .ECC_WIDTH(ECC_WIDTH),
    .nCK_PER_CLK(nCK_PER_CLK)
  ) mig_7series_v2_0_ecc_merge_enc_sva_i (
    .clk(clk),
    .rst(rst),
    .wr_data(wr_data),
    .wr_data_mask(wr_data_mask),
    .rd_merge_data(rd_merge_data),
    .wr_data_r(wr_data_r),
    .wr_data_mask_r(wr_data_mask_r),
    .rd_merge_data_r(rd_merge_data_r),
    .h_rows(h_rows),
    .raw_not_ecc(raw_not_ecc),
    .raw_not_ecc_r(raw_not_ecc_r),
    .mc_wrdata(mc_wrdata),
    .mc_wrdata_mask(mc_wrdata_mask)
  );