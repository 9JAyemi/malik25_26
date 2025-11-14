// SVA for ones_counter, triple_counter, top_module, and DFF
// Bind these into the DUT. Focused, high-signal-quality checks + core coverage.

////////////////////////////////////////////////////////////
// ones_counter SVA
////////////////////////////////////////////////////////////
module oc_sva();
  // Bound into ones_counter scope; can directly see clk,in,shift_reg,temp_count,count
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Elaboration-time width sanity (will flag the truncation bug)
  initial begin
    if ($bits({shift_reg[6:0], in}) != $bits(shift_reg))
      $error("ones_counter: width mismatch in shift_reg update (%0d != %0d)",
             $bits({shift_reg[6:0], in}), $bits(shift_reg));
  end

  // Shift register next-state (with explicit truncation to catch unintended behavior)
  assert property (disable iff (!past_valid || $isunknown({in,shift_reg}))
                   shift_reg == $past({shift_reg[6:0], in}[7:0]))
    else $error("ones_counter: shift_reg next-state mismatch");

  // Output next-state recurrence from prior state
  assert property (disable iff (!past_valid || $isunknown({shift_reg,count}))
                   count == (($past(shift_reg[7:5]) == 3'b111) ? ($past(count) + 4'd1) : 4'd0))
    else $error("ones_counter: count next-state mismatch");

  // Coherency: registered output mirrors internal temp_count
  assert property (disable iff (!past_valid) count == temp_count)
    else $error("ones_counter: count != temp_count");

  // No-X on output after first cycle
  assert property (disable iff (!past_valid) !$isunknown(count))
    else $error("ones_counter: X on count");

  // Coverage
  cover property (disable iff (!past_valid) count == $past(count) + 1); // increment path
  cover property (disable iff (!past_valid)
                  ($past(shift_reg[7:5]) != 3'b111) && (count == 0));   // clear path
  cover property (disable iff (!past_valid)
                  ($past(count) == 4'hF) && ($past(shift_reg[7:5]) == 3'b111) && (count == 4'h0)); // wrap
endmodule

bind ones_counter oc_sva oc_sva_i();

////////////////////////////////////////////////////////////
// triple_counter SVA
////////////////////////////////////////////////////////////
module tc_sva();
  // Bound into triple_counter; can directly see clk,in,shift_reg,temp_count,triple_count,ones_count
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Elaboration-time width sanity (will flag the truncation bug)
  initial begin
    if ($bits({shift_reg[6:0], in}) != $bits(shift_reg))
      $error("triple_counter: width mismatch in shift_reg update (%0d != %0d)",
             $bits({shift_reg[6:0], in}), $bits(shift_reg));
  end

  // Shift register next-state (explicit truncation)
  assert property (disable iff (!past_valid || $isunknown({in,shift_reg}))
                   shift_reg == $past({shift_reg[6:0], in}[7:0]))
    else $error("triple_counter: shift_reg next-state mismatch");

  // Output next-state recurrence using prior triple_count and prior gating inputs
  assert property (disable iff (!past_valid || $isunknown({shift_reg,triple_count,ones_count}))
                   triple_count == (
                     ($past(shift_reg[7:5]) == 3'b111 && $past(ones_count) >= 4'd3)
                       ? ($past(triple_count) + 3'd1)
                       : 3'd0))
    else $error("triple_counter: triple_count next-state mismatch");

  // Coherency: registered output mirrors internal temp_count
  assert property (disable iff (!past_valid) triple_count == temp_count)
    else $error("triple_counter: triple_count != temp_count");

  // No-X on output after first cycle
  assert property (disable iff (!past_valid) !$isunknown(triple_count))
    else $error("triple_counter: X on triple_count");

  // Coverage
  cover property (disable iff (!past_valid)
                  ($past(shift_reg[7:5]) == 3'b111) && ($past(ones_count) >= 3) &&
                  (triple_count == $past(triple_count) + 1)); // increment qualified by ones_count
  cover property (disable iff (!past_valid)
                  ($past(shift_reg[7:5]) == 3'b111) && ($past(ones_count) < 3) &&
                  (triple_count == 0)); // gated clear when threshold not met
  cover property (disable iff (!past_valid)
                  ($past(triple_count) == 3'd7) && ($past(shift_reg[7:5]) == 3'b111) &&
                  ($past(ones_count) >= 3) && (triple_count == 3'd0)); // wrap
endmodule

bind triple_counter tc_sva tc_sva_i();

////////////////////////////////////////////////////////////
//// DFF SVA
////////////////////////////////////////////////////////////
module dff_sva();
  // Bound into DFF; sees clk, reset, d, q
  default clocking cb @(posedge clk); endclocking

  // Async reset takes immediate effect
  assert property (@(posedge reset) q == 1'b0)
    else $error("DFF: q not 0 on reset assertion");

  // While reset is high, q must hold 0
  assert property (@(posedge clk) reset |-> (q == 1'b0))
    else $error("DFF: q not held 0 during reset");

  // On clock, when not in reset, q captures past d
  assert property (@(posedge clk) disable iff (reset) q == $past(d))
    else $error("DFF: q does not match past d");

  // No-X on q when not in reset
  assert property (@(posedge clk) disable iff (reset) !$isunknown(q))
    else $error("DFF: X on q");
endmodule

bind DFF dff_sva dff_sva_i();