// SVA checker for mux2to1
module mux2to1_sva (
  input logic in1,
  input logic in2,
  input logic sel,
  input logic out,
  input logic vpwr,
  input logic vgnd
);
  wire power_good = (vpwr === 1'b1) && (vgnd === 1'b0);

  // Use event-based sampling since design is purely combinational
  // Sample on any relevant signal activity
  `define MUX_EVT (in1 or in2 or sel or out or vpwr or vgnd)

  // Disable assertions when power is not good
  default disable iff (!power_good);

  // Functional equivalence (4-state accurate, including ?: merge behavior)
  assert property (@(`MUX_EVT) 1 |-> ##0 (out === (sel ? in2 : in1)));

  // Output must be known when inputs and select are known
  assert property (@(`MUX_EVT) !$isunknown({in1,in2,sel}) |-> ##0 !$isunknown(out));

  // With unknown sel but equal known inputs, output equals that value (merge rule)
  assert property (@(`MUX_EVT)
                   $isunknown(sel) && !$isunknown({in1,in2}) && (in1===in2)
                   |-> ##0 (out === in1));

  // Out changes only due to sel or the selected input (when sel is known)
  assert property (@(`MUX_EVT)
                   !$isunknown(sel) && $changed(out)
                   |-> ($changed(sel) ||
                        ($changed(in1) && (sel===1'b0)) ||
                        ($changed(in2) && (sel===1'b1))));

  // Coverage
  cover property (@(`MUX_EVT) sel===1'b0 ##0 (out===in1));
  cover property (@(`MUX_EVT) sel===1'b1 ##0 (out===in2));
  cover property (@(`MUX_EVT) $changed(sel)); // exercise select switching
  cover property (@(`MUX_EVT)
                  $isunknown(sel) && !$isunknown({in1,in2}) && (in1!==in2) ##0 $isunknown(out)); // X-prop case
  cover property (@(`MUX_EVT) sel===1'b0 && $changed(in2) ##0 $stable(out)); // unselected input ignored
  cover property (@(`MUX_EVT) sel===1'b1 && $changed(in1) ##0 $stable(out)); // unselected input ignored

  `undef MUX_EVT
endmodule

// Bind the checker to the DUT
bind mux2to1 mux2to1_sva u_mux2to1_sva(.*);