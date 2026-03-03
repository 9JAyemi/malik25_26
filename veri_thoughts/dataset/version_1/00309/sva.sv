// SVA for mem_soft_ecc
// Bindable, concise, and parameter-aware

module mem_soft_ecc_sva #(
  parameter int C_DATA_WIDTH  = 32,
  parameter int C_ADDRB_WIDTH = 10,
  parameter int C_HAS_SOFTECC_OUTPUT_REGS_B = 1,
  parameter int FLOP_DELAY = 100
)(
  input  logic                         CLK,
  input  logic [C_DATA_WIDTH-1:0]      DIN,
  input  logic [C_ADDRB_WIDTH-1:0]     RDADDRECC_IN,
  input  logic                         SBITERR_IN,
  input  logic                         DBITERR_IN,
  input  logic [C_DATA_WIDTH-1:0]      DOUT,
  input  logic [C_ADDRB_WIDTH-1:0]     RDADDRECC,
  input  logic                         SBITERR,
  input  logic                         DBITERR
);

  default clocking cb @(posedge CLK); endclocking

  // past_valid to avoid first-sample $past hazards
  logic past_valid;
  always_ff @(posedge CLK) past_valid <= 1'b1;

  // Basic X-prop sanity (outputs should not be X when corresponding inputs are known)
  // Combinational path: same-cycle; Registered path: one-cycle
  generate
    if (C_HAS_SOFTECC_OUTPUT_REGS_B==0) begin : comb_checks
      // Functional passthrough
      assert property (DOUT == DIN
                    && RDADDRECC == RDADDRECC_IN
                    && SBITERR == SBITERR_IN
                    && DBITERR == DBITERR_IN)
        else $error("mem_soft_ecc comb mismatch");

      // X-clean when inputs known
      assert property ((!$isunknown(DIN))        |-> (!$isunknown(DOUT)));
      assert property ((!$isunknown(RDADDRECC_IN)) |-> (!$isunknown(RDADDRECC)));
      assert property ((!$isunknown(SBITERR_IN)) |-> (!$isunknown(SBITERR)));
      assert property ((!$isunknown(DBITERR_IN)) |-> (!$isunknown(DBITERR)));

      // Coverage: observe propagation on change/pulse
      cover property ($changed(DIN)         && (DOUT==DIN));
      cover property ($changed(RDADDRECC_IN) && (RDADDRECC==RDADDRECC_IN));
      cover property ($rose(SBITERR_IN)     && SBITERR);
      cover property ($fell(SBITERR_IN)     && !SBITERR);
      cover property ($rose(DBITERR_IN)     && DBITERR);
      cover property ($fell(DBITERR_IN)     && !DBITERR);
    end
    else begin : reg_checks
      // One-cycle registered delay (assumes FLOP_DELAY < clock period)
      assert property (past_valid |-> (
                         DOUT      == $past(DIN)         &&
                         RDADDRECC == $past(RDADDRECC_IN) &&
                         SBITERR   == $past(SBITERR_IN)  &&
                         DBITERR   == $past(DBITERR_IN)))
        else $error("mem_soft_ecc reg mismatch");

      // X-clean one-cycle later when prior inputs known
      assert property (past_valid && (!$isunknown($past(DIN)))          |-> (!$isunknown(DOUT)));
      assert property (past_valid && (!$isunknown($past(RDADDRECC_IN))) |-> (!$isunknown(RDADDRECC)));
      assert property (past_valid && (!$isunknown($past(SBITERR_IN)))   |-> (!$isunknown(SBITERR)));
      assert property (past_valid && (!$isunknown($past(DBITERR_IN)))   |-> (!$isunknown(DBITERR)));

      // Coverage: observe 1-cycle propagation
      cover property ($changed(DIN)          ##1 (DOUT==$past(DIN)));
      cover property ($changed(RDADDRECC_IN) ##1 (RDADDRECC==$past(RDADDRECC_IN)));
      cover property ($rose(SBITERR_IN)      ##1 $rose(SBITERR));
      cover property ($fell(SBITERR_IN)      ##1 $fell(SBITERR));
      cover property ($rose(DBITERR_IN)      ##1 $rose(DBITERR));
      cover property ($fell(DBITERR_IN)      ##1 $fell(DBITERR));
    end
  endgenerate

endmodule

// Bind into the DUT
bind mem_soft_ecc mem_soft_ecc_sva #(
  .C_DATA_WIDTH(C_DATA_WIDTH),
  .C_ADDRB_WIDTH(C_ADDRB_WIDTH),
  .C_HAS_SOFTECC_OUTPUT_REGS_B(C_HAS_SOFTECC_OUTPUT_REGS_B),
  .FLOP_DELAY(FLOP_DELAY)
) mem_soft_ecc_sva_b (
  .CLK(CLK),
  .DIN(DIN),
  .RDADDRECC_IN(RDADDRECC_IN),
  .SBITERR_IN(SBITERR_IN),
  .DBITERR_IN(DBITERR_IN),
  .DOUT(DOUT),
  .RDADDRECC(RDADDRECC),
  .SBITERR(SBITERR),
  .DBITERR(DBITERR)
);