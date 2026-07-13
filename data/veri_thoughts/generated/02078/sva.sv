module address_decoder_sva (
  input logic address,
  input logic clock,
  input logic reset_n,
  input logic [31:0] readdata
);
  // Clock: clock (posedge). Reset: reset_n active-low async. Sequential registered output.

  // During reset, readdata must be zero.
  reset_clears_readdata: assert property (
    @(posedge clock) (!reset_n) |-> (readdata == 32'h0000_0000)
  );

  // On the cycle reset_n rises, readdata is still 0 before the update.
  reset_release_holds_zero_one_cycle: assert property (
    @(posedge clock) $rose(reset_n) |-> (readdata == 32'h0000_0000)
  );

  // If previous cycle was out of reset and address was 0, readdata now equals 0x560F6F0F.
  map_prev_addr0_to_const0: assert property (
    @(posedge clock) disable iff (!reset_n)
      ($past(reset_n) && ($past(address) == 1'b0)) |-> (readdata == 32'h560F_6F0F)
  );

  // If previous cycle was out of reset and address was 1, readdata now equals 0xADC3C2C2.
  map_prev_addr1_to_const1: assert property (
    @(posedge clock) disable iff (!reset_n)
      ($past(reset_n) && ($past(address) == 1'b1)) |-> (readdata == 32'hADC3_C2C2)
  );

  // If address is 0 this cycle, next cycle readdata is 0x560F6F0F (barring reset).
  next_cycle_update_addr0: assert property (
    @(posedge clock) disable iff (!reset_n)
      (address == 1'b0) |=> (readdata == 32'h560F_6F0F)
  );

  // If address is 1 this cycle, next cycle readdata is 0xADC3C2C2 (barring reset).
  next_cycle_update_addr1: assert property (
    @(posedge clock) disable iff (!reset_n)
      (address == 1'b1) |=> (readdata == 32'hADC3_C2C2)
  );

  // If out of reset for two cycles and address unchanged, readdata is unchanged.
  stable_when_address_unchanged: assert property (
    @(posedge clock) disable iff (!reset_n)
      ($past(reset_n) && (address == $past(address))) |-> (readdata == $past(readdata))
  );

  // If address changed in the prior cycle (vs two cycles ago) and no reset, readdata changes now.
  readdata_changes_when_addr_changed_prev: assert property (
    @(posedge clock) disable iff (!reset_n)
      ($past(reset_n,1) && $past(reset_n,2) && ($past(address,1) != $past(address,2))) |-> (readdata != $past(readdata))
  );

  // If previous address was 0 or 1 while out of reset, readdata is nonzero this cycle.
  readdata_nonzero_for_legal_prev_addr: assert property (
    @(posedge clock) disable iff (!reset_n)
      ($past(reset_n) && (($past(address) == 1'b0) || ($past(address) == 1'b1))) |-> (readdata != 32'h0000_0000)
  );

endmodule