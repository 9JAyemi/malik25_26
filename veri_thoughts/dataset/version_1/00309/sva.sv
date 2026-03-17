module mem_soft_ecc_sva
  #(
    parameter C_DATA_WIDTH = 32,
    parameter C_ADDRB_WIDTH = 10,
    parameter C_HAS_SOFTECC_OUTPUT_REGS_B = 1,
    parameter C_USE_SOFTECC = 0,
    parameter FLOP_DELAY = 100
  )
  (
    input logic                     CLK,
    input logic [C_DATA_WIDTH-1:0]  DIN,
    input logic [C_DATA_WIDTH-1:0]  DOUT,
    input logic                     SBITERR_IN,
    input logic                     DBITERR_IN,
    input logic                     SBITERR,
    input logic                     DBITERR,
    input logic [C_ADDRB_WIDTH-1:0] RDADDRECC_IN,
    input logic [C_ADDRB_WIDTH-1:0] RDADDRECC
  );

  generate
    if (C_HAS_SOFTECC_OUTPUT_REGS_B == 0) begin : gen_no_output_stage
      // DOUT directly mirrors DIN when output registers are disabled.
      check_dout_passthrough: assert property (
        @(posedge CLK) DOUT == DIN
      );

      // RDADDRECC directly mirrors RDADDRECC_IN when output registers are disabled.
      check_rdaddrecc_passthrough: assert property (
        @(posedge CLK) RDADDRECC == RDADDRECC_IN
      );

      // SBITERR directly mirrors SBITERR_IN when output registers are disabled.
      check_sbiterr_passthrough: assert property (
        @(posedge CLK) SBITERR == SBITERR_IN
      );

      // DBITERR directly mirrors DBITERR_IN when output registers are disabled.
      check_dbiterr_passthrough: assert property (
        @(posedge CLK) DBITERR == DBITERR_IN
      );
    end
  endgenerate

  generate
    if (C_HAS_SOFTECC_OUTPUT_REGS_B == 1) begin : gen_has_output_stage
      // DOUT reflects the previous-cycle DIN when output registers are enabled.
      check_dout_registered: assert property (
        @(posedge CLK) 1'b1 |=> DOUT == $past(DIN)
      );

      // RDADDRECC reflects the previous-cycle RDADDRECC_IN when output registers are enabled.
      check_rdaddrecc_registered: assert property (
        @(posedge CLK) 1'b1 |=> RDADDRECC == $past(RDADDRECC_IN)
      );

      // SBITERR reflects the previous-cycle SBITERR_IN when output registers are enabled.
      check_sbiterr_registered: assert property (
        @(posedge CLK) 1'b1 |=> SBITERR == $past(SBITERR_IN)
      );

      // DBITERR reflects the previous-cycle DBITERR_IN when output registers are enabled.
      check_dbiterr_registered: assert property (
        @(posedge CLK) 1'b1 |=> DBITERR == $past(DBITERR_IN)
      );
    end
  endgenerate

endmodule