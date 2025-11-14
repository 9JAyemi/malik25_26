// SVA for mux4to1_enable
`ifndef MUX4TO1_ENABLE_SVA
`define MUX4TO1_ENABLE_SVA

module mux4to1_enable_sva;

  // Sample on any relevant combinational change
  `define MON_EV (data0 or data1 or data2 or data3 or sel or enable or out or sel_inv or mux_out)

  // Enable forces output low
  assert property (@(`MON_EV) (enable===1'b1) |-> (out===1'b0));

  // Functional mapping (enabled path uses LSB of selected data)
  assert property (@(`MON_EV) (enable===1'b0 && sel===2'b00) |-> (out===data0[0]));
  assert property (@(`MON_EV) (enable===1'b0 && sel===2'b01) |-> (out===data1[0]));
  assert property (@(`MON_EV) (enable===1'b0 && sel===2'b10) |-> (out===data2[0]));
  assert property (@(`MON_EV) (enable===1'b0 && sel===2'b11) |-> (out===data3[0]));

  // Out equals internal mux_out selection when enabled and sel known
  assert property (@(`MON_EV) (enable===1'b0 && !$isunknown(sel)) |-> (out===mux_out[sel]));

  // One-hot decode correctness when sel is 2-state
  assert property (@(`MON_EV)
    (!$isunknown(sel)) |->
      $onehot({sel_inv[1]&sel_inv[0],
               sel_inv[1]&sel[0],
               sel[1]&sel_inv[0],
               sel[1]&sel[0]}));

  // Internal mux_out bits match spec (note: only LSB of dataN is used by DUT)
  assert property (@(`MON_EV) mux_out[0] === ((sel_inv[1] & sel_inv[0]) ? data0[0] : 1'bx));
  assert property (@(`MON_EV) mux_out[1] === ((sel_inv[1] & sel[0])    ? data1[0] : 1'bx));
  assert property (@(`MON_EV) mux_out[2] === ((sel[1]    & sel_inv[0]) ? data2[0] : 1'bx));
  assert property (@(`MON_EV) mux_out[3] === ((sel[1]    & sel[0])     ? data3[0] : 1'bx));

  // X-propagation expectations
  assert property (@(`MON_EV) (enable===1'b0 && $isunknown(sel)) |-> $isunknown(out));
  assert property (@(`MON_EV)
    (enable===1'b0 && !$isunknown(sel) &&
     !$isunknown({data0[0],data1[0],data2[0],data3[0]})) |-> !$isunknown(out));

  // Coverage
  cover property (@(`MON_EV) (enable===1'b0 && sel===2'b00) ##0 (out===data0[0]));
  cover property (@(`MON_EV) (enable===1'b0 && sel===2'b01) ##0 (out===data1[0]));
  cover property (@(`MON_EV) (enable===1'b0 && sel===2'b10) ##0 (out===data2[0]));
  cover property (@(`MON_EV) (enable===1'b0 && sel===2'b11) ##0 (out===data3[0]));
  cover property (@(`MON_EV) (enable===1'b1) ##0 (out===1'b0));
  cover property (@(`MON_EV) (enable===1'b0 && $isunknown(sel)) ##0 $isunknown(out));

  `undef MON_EV
endmodule

bind mux4to1_enable mux4to1_enable_sva u_mux4to1_enable_sva();

`endif