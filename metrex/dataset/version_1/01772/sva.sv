// SVA for serializer. Bind this to the DUT.
// Focus: counter behavior, reset semantics, range/sanity, data mapping, and key coverage.

module serializer_sva #(
  parameter int DWIDTH = 64
)(
  input  wire        fast_clk,
  input  wire        res_n,
  input  wire [DWIDTH-1:0] data_in,
  input  wire        data_out,
  input  wire [7:0]  curr_bit
);

  // Static param sanity: 8-bit counter must be able to cover DWIDTH-1
  initial begin
    assert (DWIDTH >= 1 && DWIDTH <= 256)
      else $error("serializer: DWIDTH (%0d) must be in [1..256] for 8-bit curr_bit", DWIDTH);
  end

  default clocking cb @(posedge fast_clk); endclocking

  // Reset behavior
  // On any cycle with reset low, next cycle curr_bit must be 0
  assert property (!res_n |=> curr_bit == 0);

  // While reset is held low across cycles, curr_bit is 0 every cycle
  assert property ((!res_n && $past(!res_n)) |-> curr_bit == 0);

  // Counter stays in range and known when enabled
  assert property (disable iff (!res_n) curr_bit < DWIDTH);
  assert property (disable iff (!res_n) !$isunknown(curr_bit));

  // Step or wrap: when enabled, either increment by 1 or wrap to 0 after DWIDTH-1
  assert property (
    (res_n && $past(res_n)) |-> (
      ($past(curr_bit) == DWIDTH-1) ? (curr_bit == 0) : (curr_bit == $past(curr_bit)+1)
    )
  );

  // Functional mapping: output bit equals selected input bit (bit-accurate, including X/Z)
  assert property (data_out === data_in[curr_bit]);

  // Key coverage
  cover property ($fell(res_n));
  cover property ($rose(res_n));
  // See a wrap event (DWIDTH-1 -> 0)
  cover property (disable iff (!res_n) curr_bit == DWIDTH-1 ##1 curr_bit == 0);
  // See a full frame from 0 up to DWIDTH-1 (order implied by step assertion), then wrap
  cover property (disable iff (!res_n)
                  curr_bit == 0 ##[1:DWIDTH-1] curr_bit == DWIDTH-1 ##1 curr_bit == 0);

endmodule

// Bind into DUT
bind serializer serializer_sva #(.DWIDTH(DWIDTH)) u_serializer_sva (
  .fast_clk (fast_clk),
  .res_n    (res_n),
  .data_in  (data_in),
  .data_out (data_out),
  .curr_bit (curr_bit)
);