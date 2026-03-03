// SVA for module filter
// Bind as: bind filter filter_sva #(.W(32)) u_filter_sva (.*);

module filter_sva #(parameter int W=32)
(
  input logic                 clock,
  input logic [W-1:0]         indata,
  input logic [W-1:0]         indata180,
  input logic [W-1:0]         outdata,
  input logic [W-1:0]         dly_indata,
  input logic [W-1:0]         dly_indata180
);

  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clock) past_valid <= 1'b1;

  default clocking cb @(posedge clock); endclocking

  // Pipeline register correctness
  assert property (past_valid |-> dly_indata   === $past(indata))
    else $error("dly_indata != $past(indata)");

  assert property (past_valid |-> dly_indata180 === $past(indata180))
    else $error("dly_indata180 != $past(indata180)");

  // Functional next-state of outdata
  assert property (past_valid |-> outdata ===
                   (($past(outdata) | $past(dly_indata) | $past(indata)) & $past(dly_indata180)))
    else $error("outdata next-state mismatch");

  // Invariant: mask gates outputs (no bit can be 1 where prior mask bit was 0)
  assert property (past_valid |-> ((~$past(dly_indata180)) & outdata) == '0)
    else $error("Masked-off bit set in outdata");

  // Useful covers
  // Any bit rises in outdata
  cover property (past_valid && (|(~$past(outdata) & outdata)));
  // Any bit falls in outdata
  cover property (past_valid && (|($past(outdata) & ~outdata)));
  // Mask actively blocks at least one 1 from OR-sources
  cover property (past_valid &&
                  (|((~$past(dly_indata180)) &
                     ($past(outdata) | $past(dly_indata) | $past(indata)))));
  // Inputs toggle to exercise pipelines
  cover property (past_valid && $changed(indata));
  cover property (past_valid && $changed(indata180));

endmodule