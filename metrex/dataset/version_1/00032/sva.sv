// SVA for mux4x1
// Bind into DUT for automatic checking

module mux4x1_sva (
  input  [1:0] sel,
  input  [3:0] din,
  input        dout
);

  // Functional equivalence: dout must reflect the selected bit (including X/Z propagation)
  property p_func_eq;
    @(sel or din) 1'b1 |-> ##0 (dout === din[sel]);
  endproperty
  assert property (p_func_eq)
    else $error("mux4x1: dout != din[sel]");

  // Selector must be known (prevents stale/latch-like behavior on X/Z selector)
  assert property (@(sel) !$isunknown(sel))
    else $error("mux4x1: sel has X/Z");

  // If selector and selected data bit are known, dout must be known
  assert property (@(sel or din)
                   (!$isunknown(sel) && !$isunknown(din[sel])) |-> ##0 !$isunknown(dout))
    else $error("mux4x1: dout unknown despite known selected input");

  // Minimal functional coverage: each select path exercised and correct
  cover property (@(sel or din) (sel == 2'b00) ##0 (dout === din[0]));
  cover property (@(sel or din) (sel == 2'b01) ##0 (dout === din[1]));
  cover property (@(sel or din) (sel == 2'b10) ##0 (dout === din[2]));
  cover property (@(sel or din) (sel == 2'b11) ##0 (dout === din[3]));

endmodule

bind mux4x1 mux4x1_sva mux4x1_sva_i (.sel(sel), .din(din), .dout(dout));