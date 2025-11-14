// SVA for dna_sequencer
module dna_sequencer_sva #(parameter [95:0] SIM_DNA_VALUE = 96'h0);

  // Bound into dna_sequencer: has direct visibility of CLK, READ, SHIFT, DIN, DOUT, dna_val
  localparam int W = $bits(dna_val);

  bit past_valid;
  initial past_valid = 0;
  always @(posedge CLK) past_valid <= 1'b1;

  // No X/Z on control/data
  assert property (@(posedge CLK) !$isunknown({READ, SHIFT, DIN}));

  // DOUT reflects current LSB of dna_val after the tick
  assert property (@(posedge CLK) 1 |-> ##0 (DOUT === dna_val[0]));

  // READ loads constant and sets DOUT to its LSB (priority over SHIFT)
  assert property (@(posedge CLK) READ |-> ##0
                   (dna_val === SIM_DNA_VALUE && DOUT === SIM_DNA_VALUE[0]));

  // SHIFT (when !READ) right-shifts and sets DOUT to new LSB (= prior bit1)
  assert property (@(posedge CLK) disable iff (!past_valid)
                   (!READ && SHIFT) |-> ##0
                   (dna_val === {DIN, $past(dna_val[W-1:1])} &&
                    DOUT   === $past(dna_val[1])));

  // Hold when idle
  assert property (@(posedge CLK) disable iff (!past_valid)
                   (!READ && !SHIFT) |-> ##0 ($stable(dna_val) && $stable(DOUT)));

  // DIN must be known when shifting
  assert property (@(posedge CLK) (!READ && SHIFT) |-> !$isunknown(DIN));

  // Coverage
  cover property (@(posedge CLK) READ);
  cover property (@(posedge CLK) (!READ && SHIFT));
  cover property (@(posedge CLK) (!READ && !SHIFT));
  cover property (@(posedge CLK) (READ ##1 (!READ && SHIFT)));     // priority scenario
  cover property (@(posedge CLK) disable iff (!past_valid)
                  (!READ && SHIFT)[*W]);                           // 96 consecutive shifts

endmodule

bind dna_sequencer dna_sequencer_sva #(.SIM_DNA_VALUE(SIM_DNA_VALUE)) dna_sequencer_sva_i();