// SVA for cf_jesd_align_2
module cf_jesd_align_2_sva
(
  input         rx_clk,
  input  [3:0]  rx_sof,
  input  [3:0]  rx_eof,
  input  [3:0]  rx_ferr,
  input  [31:0] rx_fdata,
  input         rx_err,
  input  [31:0] rx_data
);

  localparam [3:0] PAT0 = 4'b0101;
  localparam [3:0] PAT1 = 4'b1010;

  logic pv1, pv2;
  always_ff @(posedge rx_clk) begin
    pv1 <= 1'b1;
    pv2 <= pv1;
  end

  // Valid pattern 0101: next-cycle outputs reflect this cycle's inputs
  assert property (@(posedge rx_clk)
    (rx_sof == PAT0)
    |=> ( rx_err == ( (($past(rx_sof) == ~$past(rx_eof)) && ($past(rx_ferr)==4'd0)) ? 1'b0 : 1'b1 )
       && rx_data == $past(rx_fdata)));

  // Valid pattern 1010: next-cycle outputs use current low 24b and the byte from two cycles ago
  assert property (@(posedge rx_clk)
    (pv2 && rx_sof == PAT1)
    |=> ( rx_err == ( (($past(rx_sof) == ~$past(rx_eof)) && ($past(rx_ferr)==4'd0)) ? 1'b0 : 1'b1 )
       && rx_data == { $past(rx_fdata[23:0]), $past(rx_fdata[31:24],2) }));

  // Default (illegal) pattern: force error and 0x0000_FFFF data
  assert property (@(posedge rx_clk)
    (rx_sof != PAT0 && rx_sof != PAT1)
    |=> (rx_err == 1'b1 && rx_data == 32'h0000_ffff));

  // No false OK: rx_err can be 0 only if prior cycle was a valid, error-free frame with mutual exclusivity
  assert property (@(posedge rx_clk)
    (pv1 && rx_err == 1'b0)
    |-> ($past(rx_sof) inside {PAT0,PAT1}) && ($past(rx_sof) == ~$past(rx_eof)) && ($past(rx_ferr) == 4'd0));

  // Coverage
  cover property (@(posedge rx_clk)
    (rx_sof == PAT0 && rx_sof == ~rx_eof && rx_ferr == 0) |=> (rx_err == 0));

  cover property (@(posedge rx_clk)
    (rx_sof == PAT1 && rx_sof == ~rx_eof && rx_ferr == 0) |=> (rx_err == 0));

  cover property (@(posedge rx_clk)
    (rx_sof inside {PAT0,PAT1} && rx_ferr != 0) |=> (rx_err == 1));

  cover property (@(posedge rx_clk)
    (rx_sof inside {PAT0,PAT1} && rx_sof != ~rx_eof) |=> (rx_err == 1));

  cover property (@(posedge rx_clk)
    (rx_sof != PAT0 && rx_sof != PAT1) |=> (rx_err == 1 && rx_data == 32'h0000_ffff));

endmodule

// Bind into the DUT
bind cf_jesd_align_2 cf_jesd_align_2_sva sva_i
(
  .rx_clk  (rx_clk),
  .rx_sof  (rx_sof),
  .rx_eof  (rx_eof),
  .rx_ferr (rx_ferr),
  .rx_fdata(rx_fdata),
  .rx_err  (rx_err),
  .rx_data (rx_data)
);