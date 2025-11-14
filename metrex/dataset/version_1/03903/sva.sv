// SVA for not_32: bindable, concise, full functional/X-prop checks and coverage

bind not_32 not_32_sva u_not_32_sva (.a(a), .out(out));

module not_32_sva (input logic [31:0] a, out);

  // Functional equivalence (4-state) – evaluate after delta to avoid race
  assert property (@(a or out) 1'b1 |-> ##0 (out === ~a))
    else $error("not_32: out must be bitwise NOT of a (4-state)");

  // If input vector is fully known, output must be fully known and 2-state correct
  assert property (@(a or out) ##0 (!$isunknown(a) |-> (!$isunknown(out) && out == ~a)))
    else $error("not_32: known a must yield known, correct out");

  // Output must only change when input changes
  assert property (@(a or out) ##0 ($changed(out) |-> $changed(a)))
    else $error("not_32: out changed without change on a");

  // Per-bit checks and coverage
  genvar i;
  for (i=0; i<32; i++) begin : g_bit
    // Bit accuracy (4-state)
    assert property (@(a[i] or out[i]) 1'b1 |-> ##0 (out[i] === ~a[i]))
      else $error("not_32: bit %0d mismatch", i);

    // X/Z propagation: X/Z on input bit must yield X on output bit
    assert property (@(a[i] or out[i]) ##0 ($isunknown(a[i]) |-> $isunknown(out[i])))
      else $error("not_32: bit %0d X/Z must propagate", i);

    // Coverage: observe both mappings and X-prop per bit
    cover property (@(a[i]) ##0 (a[i] == 1'b0 && out[i] == 1'b1));
    cover property (@(a[i]) ##0 (a[i] == 1'b1 && out[i] == 1'b0));
    cover property (@(a[i]) ##0 ($isunknown(a[i]) && $isunknown(out[i])));
  end

  // Whole-word corner covers
  cover property (@(a or out) ##0 (a == 32'h0000_0000 && out == 32'hFFFF_FFFF));
  cover property (@(a or out) ##0 (a == 32'hFFFF_FFFF && out == 32'h0000_0000));

endmodule