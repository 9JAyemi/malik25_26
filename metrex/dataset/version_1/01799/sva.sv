// Assertions for address_decoder
module address_decoder_sva(
  input logic        clock,
  input logic [14:0] address,
  input logic [11:0] q
);
  default clocking cb @(posedge clock); endclocking

  // Functional correctness (next-cycle behavior)
  a_low:  assert property (address < 15'h0800                           |=> q == 12'h000);
  a_mid:  assert property (address >= 15'h0800 && address < 15'h1000     |=> q == $past(address[11:0]));
  a_high: assert property (address >= 15'h1000                           |=> q == $past(address[14:3]));

  // Knownness: if input is known, output becomes known next cycle
  a_no_x: assert property (!$isunknown(address) |=> !$isunknown(q));

  // Coverage: hit all regions and key boundaries
  c_low_range:  cover property (address < 15'h0800);
  c_mid_range:  cover property (address >= 15'h0800 && address < 15'h1000);
  c_high_range: cover property (address >= 15'h1000);

  c_b_07FF:  cover property (address == 15'h07FF  |=> q == 12'h000);
  c_b_0800:  cover property (address == 15'h0800  |=> q == $past(address[11:0]));
  c_b_0FFF:  cover property (address == 15'h0FFF  |=> q == $past(address[11:0]));
  c_b_1000:  cover property (address == 15'h1000  |=> q == $past(address[14:3]));
  c_b_7FFF:  cover property (address == 15'h7FFF  |=> q == $past(address[14:3]));
endmodule

// Bind into DUT
bind address_decoder address_decoder_sva sva(.clock(clock), .address(address), .q(q));