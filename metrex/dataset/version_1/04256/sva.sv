// SVA for tai_counter
// Bind this file to the DUT
//   bind tai_counter tai_counter_sva #(.SYSCLK_FREQ(SYSCLK_FREQ)) u_tai_counter_sva (.*);

module tai_counter_sva #(parameter int unsigned SYSCLK_FREQ = 32'd100_000_000)
(
  input  logic         clk_in,
  input  logic         pps_in,
  input  logic         cnt_ena_in,
  input  logic         pps_bypass_in,
  input  logic         clr_n_in,
  input  logic         load_sec_in,
  input  logic         load_nanosec_in,
  input  logic [63:0]  sec_data_in,
  input  logic [31:0]  nanosec_data_in,
  output logic [63:0]  sec_data_out,
  output logic [31:0]  nanosec_data_out
);

  // These names (seconds, nanoseconds, load_*_p/l, nano_counter_carry, nano_counter_clr)
  // are internal to the DUT and are visible via bind.

  default disable iff (!clr_n_in)

  // ---------------------------
  // Basic combinational ties
  // ---------------------------
  // Outputs reflect internal regs
  assert property (@(posedge clk_in)  sec_data_out     == seconds);
  assert property (@(posedge clk_in)  nanosec_data_out == nanoseconds);

  // Carry definition and clear pipeline relation
  assert property (@(posedge clk_in)  (nanoseconds <  SYSCLK_FREQ-1) |-> (nano_counter_carry == 1'b0));
  assert property (@(posedge clk_in)  (nanoseconds >= SYSCLK_FREQ-1) |-> (nano_counter_carry == 1'b1));
  assert property (@(posedge clk_in)  nano_counter_clr == !$past(nano_counter_carry));

  // Async clear forces nanoseconds to 0 at the negedge of nano_counter_clr
  assert property (@(negedge nano_counter_clr) nanoseconds == 32'b0);

  // ---------------------------
  // Synchronizers / edge detectors in clk_in domain
  // ---------------------------
  assert property (@(posedge clk_in) load_sec_l      == $past(load_sec_p));
  assert property (@(posedge clk_in) load_nanosec_l  == $past(load_nanosec_p));
  assert property (@(posedge clk_in) load_sec_p      == $past(load_sec_in));
  assert property (@(posedge clk_in) load_nanosec_p  == $past(load_nanosec_in));

  // One-cycle edge-detect equivalence
  assert property (@(posedge clk_in) (load_sec_l==0     && load_sec_p==1)     == $rose(load_sec_p));
  assert property (@(posedge clk_in) (load_nanosec_l==0 && load_nanosec_p==1) == $rose(load_nanosec_p));

  // ---------------------------
  // Nanoseconds counter behavior (clk_in domain)
  // ---------------------------
  // Hold when disabled (and no async clear edge)
  assert property (@(posedge clk_in)
    $past(nano_counter_clr) && nano_counter_clr && !cnt_ena_in
    |-> nanoseconds == $past(nanoseconds));

  // Load when enabled on rising edge of load pulse
  assert property (@(posedge clk_in)
    cnt_ena_in && $rose(load_nanosec_p)
    |-> nanoseconds == nanosec_data_in);

  // Ignore load when disabled
  assert property (@(posedge clk_in)
    !cnt_ena_in && $rose(load_nanosec_p)
    |-> nanoseconds == $past(nanoseconds));

  // Increment by 1 when enabled, no load, no async clear edge
  assert property (@(posedge clk_in)
    $past(nano_counter_clr) && nano_counter_clr && cnt_ena_in && !(load_nanosec_l==0 && load_nanosec_p==1)
    |-> nanoseconds == $past(nanoseconds) + 1);

  // Wrap to 0 after reaching SYSCLK_FREQ-1 when enabled and not loading
  assert property (@(posedge clk_in)
    $past(nanoseconds) == SYSCLK_FREQ-1 && $past(cnt_ena_in) && !$past($rose(load_nanosec_p))
    |-> nanoseconds == 32'd0);

  // Reset effects in clk domain
  assert property (@(posedge clk_in)
    !clr_n_in |-> (nanoseconds==32'd0 && nano_counter_clr==1'b0 &&
                   load_sec_l==1'b0 && load_sec_p==1'b0 &&
                   load_nanosec_l==1'b0 && load_nanosec_p==1'b0));

  // ---------------------------
  // Seconds counter behavior (pps_in domain)
  // ---------------------------
  // Reset in pps domain
  assert property (@(posedge pps_in) !clr_n_in |-> seconds == 64'd0);

  // Hold when disabled (regardless of load)
  assert property (@(posedge pps_in) !cnt_ena_in |-> seconds == $past(seconds));

  // Load when enabled and load edge observed
  assert property (@(posedge pps_in)
    cnt_ena_in && (load_sec_l==0 && load_sec_p==1)
    |-> seconds == sec_data_in);

  // Increment when enabled and no load edge observed
  assert property (@(posedge pps_in)
    cnt_ena_in && !(load_sec_l==0 && load_sec_p==1)
    |-> seconds == $past(seconds) + 1);

  // ---------------------------
  // X/Z cleanliness after reset deassertion
  // ---------------------------
  assert property (@(posedge clk_in)  !$isunknown({nano_counter_clr,nanoseconds,load_sec_l,load_sec_p,load_nanosec_l,load_nanosec_p}));
  assert property (@(posedge pps_in)  !$isunknown(seconds));

  // ---------------------------
  // Coverage
  // ---------------------------
  cover property (@(posedge clk_in)  $rose(load_nanosec_p) && cnt_ena_in);
  cover property (@(posedge clk_in)  $past(nanoseconds)==SYSCLK_FREQ-1 && $past(cnt_ena_in) ##1 nanoseconds==0);
  cover property (@(posedge pps_in)  cnt_ena_in && (load_sec_l==0 && load_sec_p==1));
  cover property (@(posedge pps_in)  cnt_ena_in && !(load_sec_l==0 && load_sec_p==1) && seconds==$past(seconds)+1);
  cover property (@(posedge clk_in)  !cnt_ena_in && $past(nano_counter_clr) && nano_counter_clr && nanoseconds==$past(nanoseconds));
  cover property (@(posedge clk_in)  !clr_n_in);

endmodule

bind tai_counter tai_counter_sva #(.SYSCLK_FREQ(SYSCLK_FREQ)) u_tai_counter_sva (.*);