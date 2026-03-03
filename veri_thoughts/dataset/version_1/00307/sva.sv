// SVA for module complement
// Bind this checker to the DUT to verify timing/functional intent concisely.

module complement_sva (
  input  logic CLK,
  input  logic D,
  input  logic Q,
  input  logic reg1,
  input  logic reg2
);
  default clocking cb @(posedge CLK); endclocking

  // Guard for $past
  logic past1, past2;
  always_ff @(posedge CLK) begin
    past1 <= 1'b1;
    past2 <= past1;
  end

  // reg1 must capture D each cycle
  assert property (disable iff (!past1) reg1 == $past(D))
    else $error("reg1 did not capture D");

  // Q must follow prior reg1 each cycle
  assert property (disable iff (!past1) Q == $past(reg1))
    else $error("Q did not follow reg1 (1-cycle)");

  // Optional direct D->Q 1-cycle latency check (enabled after 2 clocks)
  assert property (disable iff (!past2) Q == $past(D))
    else $error("Q did not reflect prior D (1-cycle)");

  // Knownness (catch X/Z) after pipeline fills
  assert property (disable iff (!past1) !$isunknown(reg1))
    else $error("reg1 is X/Z");
  assert property (disable iff (!past2) !$isunknown(Q))
    else $error("Q is X/Z after latency");

  // reg2 consistency: due to multiple synchronous drivers, reg2 can become either
  // the toggle of its prior value or the prior reg1 value. It must be one of them.
  // This both documents and constrains the ambiguous behavior.
  assert property (disable iff (!past1)
                   (reg2 == ~$past(reg2)) || (reg2 == $past(reg1)))
    else $error("reg2 inconsistent with either toggle or reg1");

  // Coverage: exercise 0->1 and 1->0 on D and observe Q next cycle
  cover property (disable iff (!past2) $rose(D) |=> Q == 1'b1);
  cover property (disable iff (!past2) $fell(D) |=> Q == 1'b0);

  // Coverage: observe both possible reg2 resolutions (if they occur)
  cover property (disable iff (!past1) reg2 == ~$past(reg2));   // toggle won
  cover property (disable iff (!past1) reg2 == $past(reg1));    // reg1 assignment won
endmodule

// Bind to the DUT (place in a separate bind file or testbench)
bind complement complement_sva u_complement_sva (
  .CLK (CLK),
  .D   (D),
  .Q   (Q),
  .reg1(reg1),
  .reg2(reg2)
);