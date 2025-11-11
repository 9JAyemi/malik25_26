// SVA checker for mig_7series_v2_0_fi_xor
// Bind this module to the DUT to verify behavior.

module mig_7series_v2_0_fi_xor_sva #(
  parameter int DQ_WIDTH    = 72,
  parameter int DQS_WIDTH   = 9,
  parameter int nCK_PER_CLK = 4
)(
  input  logic                              clk,
  input  logic                              wrdata_en,
  input  logic [2*nCK_PER_CLK*DQ_WIDTH-1:0] wrdata_in,
  input  logic [DQS_WIDTH-1:0]              fi_xor_we,
  input  logic [DQ_WIDTH-1:0]               fi_xor_wrdata,
  input  logic [DQ_WIDTH-1:0]               fi_xor_data,   // internal reg from DUT
  input  logic [2*nCK_PER_CLK*DQ_WIDTH-1:0] wrdata_out
);

  localparam int DQ_PER_DQS = DQ_WIDTH / DQS_WIDTH;
  localparam int UPPER_W    = (2*nCK_PER_CLK-1)*DQ_WIDTH;

  // Parameter sanity
  initial begin
    if (DQ_WIDTH % DQS_WIDTH != 0) $error("DQ_WIDTH must be divisible by DQS_WIDTH");
  end

  default clocking cb @(posedge clk); endclocking

  // Combinational mapping checks
  assert property (wrdata_out[0+:DQ_WIDTH] == (wrdata_in[0+:DQ_WIDTH] ^ fi_xor_data))
    else $error("Lower DQ XOR mapping mismatch");

  assert property (wrdata_out[DQ_WIDTH+:UPPER_W] == wrdata_in[DQ_WIDTH+:UPPER_W])
    else $error("Upper lanes must pass through unchanged");

  // fi_xor_data global zeroing on wrdata_en (priority)
  assert property (wrdata_en |=> fi_xor_data == '0)
    else $error("fi_xor_data must clear to 0 on wrdata_en");

  // Per-DQS-slice load/hold behavior
  genvar i;
  generate
    for (i = 0; i < DQS_WIDTH; i++) begin : g_sva_slice
      localparam int L = i*DQ_PER_DQS;
      // Load new data on fi_xor_we[i] when not cleared by wrdata_en
      assert property ((!wrdata_en && fi_xor_we[i]) |=> fi_xor_data[L+:DQ_PER_DQS] == fi_xor_wrdata[L+:DQ_PER_DQS])
        else $error("fi_xor_data slice %0d must load from fi_xor_wrdata on fi_xor_we", i);

      // Hold value otherwise
      assert property ((!wrdata_en && !fi_xor_we[i]) |=> $stable(fi_xor_data[L+:DQ_PER_DQS]))
        else $error("fi_xor_data slice %0d must hold without wrdata_en/fi_xor_we", i);
    end
  endgenerate

  // Known-prop checks (no X/Z on outputs when inputs driving are known)
  assert property ((!$isunknown({wrdata_in[0+:DQ_WIDTH], fi_xor_data})) |-> !$isunknown(wrdata_out[0+:DQ_WIDTH]))
    else $error("Unknowns propagated on lower XORed width");
  assert property ((!$isunknown(wrdata_in[DQ_WIDTH+:UPPER_W])) |-> !$isunknown(wrdata_out[DQ_WIDTH+:UPPER_W]))
    else $error("Unknowns propagated on upper pass-through");

  // Minimal functional coverage
  cover property (fi_xor_we != '0 && fi_xor_wrdata != '0);                // some slice loads non-zero
  cover property (wrdata_en ##1 fi_xor_data == '0);                       // global clear observed
  cover property ((fi_xor_data != '0) && (wrdata_out[0+:DQ_WIDTH] != wrdata_in[0+:DQ_WIDTH])); // XOR effect visible

endmodule

// Bind example (place in a package or a toplevel SV file):
// bind mig_7series_v2_0_fi_xor
//   mig_7series_v2_0_fi_xor_sva #(
//     .DQ_WIDTH(DQ_WIDTH),
//     .DQS_WIDTH(DQS_WIDTH),
//     .nCK_PER_CLK(nCK_PER_CLK)
//   ) mig_7series_v2_0_fi_xor_sva_i (
//     .clk        (clk),
//     .wrdata_en  (wrdata_en),
//     .wrdata_in  (wrdata_in),
//     .fi_xor_we  (fi_xor_we),
//     .fi_xor_wrdata(fi_xor_wrdata),
//     .fi_xor_data(fi_xor_data),    // internal reg
//     .wrdata_out (wrdata_out)
//   );