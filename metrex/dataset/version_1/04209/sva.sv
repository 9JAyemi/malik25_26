// SVA for bsg_channel_narrow
// Bind this file to the DUT or instantiate alongside.
// Focused, concise checks with essential coverage.

module bsg_channel_narrow_sva
  #( parameter int width_in_p    = 8
   , parameter int width_out_p   = 4
   , parameter bit lsb_to_msb_p  = 1
   )
   ( input  logic                  clk_i
   , input  logic                  reset_i
   , input  logic [width_in_p-1:0] data_i
   , input  logic                  deque_i
   , input  logic [width_out_p-1:0] data_o
   , input  logic                  deque_o
   );

  // Parameter sanity
  initial begin
    assert (width_in_p  > 0 && width_out_p > 0 && width_out_p <= width_in_p)
      else $error("bsg_channel_narrow: invalid widths (in=%0d out=%0d)", width_in_p, width_out_p);
    assert (lsb_to_msb_p == 0 || lsb_to_msb_p == 1)
      else $error("bsg_channel_narrow: lsb_to_msb_p must be 0 or 1");
  end

  // Helper: expected narrowed slice
  function automatic logic [width_out_p-1:0] exp_slice (input logic [width_in_p-1:0] di);
    if (lsb_to_msb_p)
      exp_slice = di[width_out_p-1:0];
    else
      exp_slice = di[width_in_p-1 -: width_out_p];
  endfunction

  // Asynchronous reset drives zero immediately (delta-cycle tolerant)
  assert property (@(posedge reset_i) ##0 (data_o == '0))
    else $error("data_o not cleared immediately on async reset");

  // While in reset, output is held at zero
  assert property (@(posedge clk_i) reset_i |-> (data_o == '0))
    else $error("data_o not zero during reset");

  // Registered one-cycle latency of the selected slice (handles first non-reset cycle)
  assert property (@(posedge clk_i) disable iff (reset_i)
                   data_o == $past(exp_slice(data_i), 1, reset_i))
    else $error("data_o mismatch with narrowed data_i (1-cycle latency)");

  // deque passthrough (no latency)
  assert property (@(posedge clk_i) (deque_o == deque_i))
    else $error("deque_o must equal deque_i");

  // No X/Z on outputs
  assert property (@(posedge clk_i) !$isunknown({data_o,deque_o}))
    else $error("Unknown (X/Z) detected on outputs");

  // Minimal but meaningful coverage
  cover property (@(posedge reset_i) 1);                        // saw reset
  cover property (@(posedge clk_i) $fell(reset_i));             // reset release
  cover property (@(posedge clk_i) disable iff (reset_i)
                  data_o == $past(exp_slice(data_i), 1, reset_i) && data_o != '0); // non-zero mapped transfer
  cover property (@(posedge clk_i) $changed(deque_i));          // deque activity
  cover property (@(posedge clk_i) disable iff (reset_i) $changed(data_o)); // output activity

endmodule

// Bind into the DUT (uncomment if you prefer automatic binding)
// bind bsg_channel_narrow bsg_channel_narrow_sva #(.width_in_p(width_in_p),
//                                                  .width_out_p(width_out_p),
//                                                  .lsb_to_msb_p(lsb_to_msb_p))
// (.*);