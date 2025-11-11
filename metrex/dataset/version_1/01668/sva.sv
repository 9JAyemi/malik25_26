// SVA for AdlerChecksum
// Bind into the DUT; checks internal math as implemented, output flags, X-safety, and basic coverage.

`ifndef ADLER_SVA
`define ADLER_SVA

// Bind this SVA to every AdlerChecksum instance
bind AdlerChecksum AdlerChecksum_sva #(.n(n)) u_adler_sva();

module AdlerChecksum_sva #(parameter int n = 16) ();

  // Access bound instance signals directly (same scope)
  // clk, data_in, checksum, checksum_result, data_valid, error_detected, A, B exist in the bound instance

  default clocking cb @(posedge clk); endclocking

  // Convenience
  logic [7:0] last_byte;
  assign last_byte = data_in[(n*8)-8 +: 8];

  // X-safety on key outputs and internal state
  assert property ( !$isunknown({checksum_result, data_valid, error_detected, A, B}) );

  // A/B are always reduced mod 251
  assert property ( !$isunknown(A) |-> (A <= 8'd250) );
  assert property ( !$isunknown(B) |-> (B <= 8'd250) );

  // As-coded next-state math (due to NBAs inside loop):
  // A_next = (A_prev + last_byte) % 251
  // B_next = (B_prev + A_prev) % 251
  assert property ( !$isunknown({$past(A), last_byte}) |-> A == (($past(A) + last_byte) % 251) );
  assert property ( !$isunknown({$past(B), $past(A)}) |-> B == (($past(B) + $past(A)) % 251) );

  // checksum_result packs B||A (same cycle as A/B update)
  assert property ( !$isunknown({A,B}) |-> checksum_result == {B, A} );

  // Flags are consistent with prior-cycle checksum_result comparison (due to separate always blocks)
  assert property ( data_valid == ($past(checksum_result) == checksum) );
  assert property ( error_detected == ($past(checksum_result) != checksum) );
  // Mutual exclusion and complement
  assert property ( !(data_valid && error_detected) );
  assert property ( data_valid == ~error_detected );

  // Basic functional coverage
  cover property ( data_valid );
  cover property ( error_detected );
  cover property ( checksum_result == checksum );
  cover property ( checksum_result != checksum );
  cover property ( last_byte == 8'h00 );
  cover property ( last_byte == 8'hFF );
  cover property ( A == 8'd0 );
  cover property ( A == 8'd250 );
  cover property ( B == 8'd0 );
  cover property ( B == 8'd250 );
  // Observe both outcomes across time
  cover property ( data_valid ##1 error_detected );
  cover property ( error_detected ##1 data_valid );

endmodule

`endif // ADLER_SVA