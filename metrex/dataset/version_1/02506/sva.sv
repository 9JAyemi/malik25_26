// Drop this SVA block inside the DUT (RstQ visibility used). Concise, high-quality checks.

initial assert (RESET_PERIOD >= 1)
  else $error("RESET_PERIOD must be >= 1");

// past-valid guard to use $past safely
logic __past_valid;
initial __past_valid = 1'b0;
always @(posedge CLK_I) __past_valid <= 1'b1;

default clocking cb @(posedge CLK_I); endclocking
default disable iff (!__past_valid);

// Basic sanity/known checks
a_known_io:      assert (!$isunknown({RST_I, SRST_O}));
a_r0_const_0:    assert (RstQ[0] == 1'b0 && $stable(RstQ[0]));
a_out_maps_top:  assert (SRST_O == RstQ[RESET_PERIOD]);

// Output must be 1 whenever synchronous reset input is 1
a_out_high_on_rst: assert (RST_I |-> SRST_O);

// Internal pipeline behavior
genvar gj;
generate
  for (gj = 1; gj < RESET_PERIOD+1; gj++) begin : gen_sva_stages
    a_set_ones_on_rst: assert (RST_I |-> (RstQ[gj] == 1'b1));
    a_shift_on_low:    assert (!RST_I |-> (RstQ[gj] == $past(RstQ[gj-1])));
  end
endgenerate

// Exact deassertion timing when reset stays low long enough:
// After a falling edge of RST_I followed by RESET_PERIOD lows,
// SRST_O stays high for exactly RESET_PERIOD cycles then goes low.
sequence s_low_run_N; !RST_I[*RESET_PERIOD]; endsequence
a_deassert_exact_len: assert ( $fell(RST_I) ##0 s_low_run_N
                               |-> SRST_O[*RESET_PERIOD] ##1 !SRST_O );

// Once SRST_O is low and reset input stays low, it must remain low
a_sticky_low: assert ((!RST_I && !SRST_O) |-> ##1 !SRST_O);

// Coverage
c_rst_rise:           cover ($rose(RST_I));
c_rst_fall:           cover ($fell(RST_I));
c_single_pulse_len:   cover ($rose(RST_I) ##1 !RST_I[*RESET_PERIOD] ##1 !SRST_O);
c_reassert_early:     cover ($fell(RST_I) ##[1:RESET_PERIOD-1] $rose(RST_I));