// SVA for rng. Bind this module to the DUT (see bind example at bottom).
module rng_sva (
  input logic        reset, rnreset,
  input logic        rngbitin, rngbitinclk,
  input logic        rngbitoutclk,
  input logic        rngbitout, rngdone,
  input logic [15:0] handle,
  // Internal DUT signals (bind to these)
  input logic [15:0] rn,
  input logic [3:0]  bitoutcounter,
  input logic        initialized
);

  // Basic combinational mappings
  assert property (@(posedge rngbitoutclk or posedge rngbitinclk)
                   handle == rn);
  assert property (@(posedge rngbitoutclk or posedge rngbitinclk)
                   rngbitout == rn[bitoutcounter]);
  assert property (@(posedge rngbitoutclk or posedge reset)
                   rngdone == (bitoutcounter == 4'd0));

  // No X on key outputs/controls
  assert property (@(posedge rngbitoutclk)
                   !$isunknown({rngdone, rngbitout, bitoutcounter, initialized}));
  assert property (@(posedge rngbitinclk or posedge rnreset)
                   !$isunknown(rn));

  // rngbitoutclk domain: reset and control
  assert property (@(posedge reset)
                   (bitoutcounter == 4'd0) && (initialized == 1'b0));

  // Initialization takes effect in the first cycle after being uninitialized
  assert property (@(posedge rngbitoutclk) disable iff (reset)
                   !$past(initialized) |-> (initialized && bitoutcounter == 4'd15));

  // Once high, initialized never de-asserts (until reset)
  assert property (@(posedge rngbitoutclk) disable iff (reset)
                   $past(initialized) |-> initialized);

  // Counter range and behavior
  assert property (@(posedge rngbitoutclk or posedge reset)
                   bitoutcounter inside {[4'd0:4'd15]});

  // Decrement while not done
  assert property (@(posedge rngbitoutclk) disable iff (reset)
                   $past(initialized) && ($past(bitoutcounter) != 4'd0)
                   |-> (bitoutcounter == $past(bitoutcounter) - 4'd1));

  // Hold at zero when done
  assert property (@(posedge rngbitoutclk) disable iff (reset)
                   $past(initialized) && ($past(bitoutcounter) == 4'd0)
                   |-> (bitoutcounter == 4'd0));

  // Liveness: after init, done must assert within 16 outclk cycles
  assert property (@(posedge rngbitoutclk) disable iff (reset)
                   $rose(initialized) |-> ##[1:16] rngdone);

  // rngbitinclk domain: rn reset and next-state function
  assert property (@(posedge rnreset) rn == 16'h0000);

  // Next-state of rn matches RTL
  assert property (@(posedge rngbitinclk) disable iff (rnreset)
    (rn[0]  == (rngbitin ^ $past(rn[15]))) &&
    (rn[1]  ==  $past(rn[0])) &&
    (rn[2]  ==  $past(rn[1])) &&
    (rn[3]  ==  $past(rn[2])) &&
    (rn[4]  ==  $past(rn[3])) &&
    (rn[5]  == ($past(rn[4])  ^ rngbitin ^ $past(rn[15]))) &&
    (rn[6]  ==  $past(rn[5])) &&
    (rn[7]  ==  $past(rn[6])) &&
    (rn[8]  ==  $past(rn[7])) &&
    (rn[9]  ==  $past(rn[8])) &&
    (rn[10] ==  $past(rn[9])) &&
    (rn[11] ==  $past(rn[10])) &&
    (rn[12] == ($past(rn[11]) ^ rngbitin ^ $past(rn[15]))) &&
    (rn[13] ==  $past(rn[12])) &&
    (rn[14] ==  $past(rn[13])) &&
    (rn[15] ==  $past(rn[14]))
  );

  // Coverage
  cover property (@(posedge rngbitoutclk) disable iff (reset)
                  $rose(initialized) ##1 (bitoutcounter == 4'd15)
                  ##14 (bitoutcounter == 4'd1)
                  ##1 (bitoutcounter == 4'd0 && rngdone));

  cover property (@(posedge rngbitinclk) disable iff (rnreset) (rngbitin == 1'b0));
  cover property (@(posedge rngbitinclk) disable iff (rnreset) (rngbitin == 1'b1));
  cover property (@(posedge rngbitoutclk) rngbitout == 1'b0);
  cover property (@(posedge rngbitoutclk) rngbitout == 1'b1);
  cover property (@(posedge rnreset) 1'b1);

endmodule

// Example bind (adjust instance path/visibility as needed):
// bind rng rng_sva u_rng_sva (.*);