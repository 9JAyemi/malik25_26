// SVA checker for lo_reg
module lo_reg_sva #(parameter WIDTH=32)
(
  input logic              clk,
  input logic              resetn, // active-low sync reset
  input logic              en,
  input logic [WIDTH-1:0]  d,
  input logic [WIDTH-1:0]  q
);

  default clocking cb @(posedge clk); endclocking

  // establish a valid past sample after first clock
  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // 1) Reset has priority and clears q to zero
  assert property ((!resetn) |-> ##0 (q == '0))
    else $error("q not cleared on reset");

  // 2) When enabled (and not in reset), q updates to sampled d on the same edge
  assert property ((resetn && en) |-> ##0 (q == $sampled(d)))
    else $error("q not updated to d when en=1");

  // 3) When not enabled (and not in reset), q holds its previous value
  assert property ((past_valid && resetn && !en) |-> ##0 (q == $past(q)))
    else $error("q changed while en=0");

  // 4) Any change of q must be due to reset or enable
  assert property ((past_valid && $changed(q)) |-> (!resetn || en))
    else $error("q changed without reset or enable");

  // 5) No X/Z on q after the clock edge
  assert property (1 |-> ##0 (!$isunknown(q)))
    else $error("q contains X/Z after clock");

  // 6) q must not change between clock edges (no mid-cycle glitches)
  assert property (@(negedge clk) $stable(q))
    else $error("q changed outside posedge clk");

  // Coverage
  cover property (!resetn);                                  // saw reset
  cover property (resetn && en ##0 (q == $sampled(d)));      // took update path
  cover property (resetn && !en);                            // took hold path
  cover property (resetn && en && ($sampled(d) != $past(q)) ##0 $changed(q) && past_valid); // visible update

endmodule

// Bind into DUT
bind lo_reg lo_reg_sva #(.WIDTH(32)) i_lo_reg_sva (.*);