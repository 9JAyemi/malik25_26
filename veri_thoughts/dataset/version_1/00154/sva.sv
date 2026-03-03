// SVA checker bound to top. Verifies inversion chain, final function (both via di and via d),
// X-behavior when inputs are known, and provides concise but complete coverage.

module top_sva_chk (
  input logic [3:0] di,
  input logic       do,
  input logic [3:0] d
);
  always_comb begin
    // Functional equivalence (4-state exact)
    assert (do === ((di[1] | di[0]) & (di[3] | di[2])))
      else $error("top SVA: do functional mismatch: di=%b do=%b", di, do);

    // Internal inversions are correct (4-state)
    assert (d === ~di)
      else $error("top SVA: d inversion mismatch: di=%b d=%b", di, d);

    // Structural net connection check via internal d
    assert (do === ~((d[1] & d[0]) | (d[3] & d[2])))
      else $error("top SVA: do vs d logic mismatch: d=%b do=%b", d, do);

    // Known-inputs imply known and correct outputs (2-state exact)
    if (!$isunknown(di)) begin
      assert (! $isunknown(d))  else $error("top SVA: d is X with known di=%b", di);
      assert (! $isunknown(do)) else $error("top SVA: do is X with known di=%b", di);
      assert (d  == ~di) else $error("top SVA: d wrong with known di=%b d=%b", di, d);
      assert (do == ((di[1] | di[0]) & (di[3] | di[2])))
        else $error("top SVA: do wrong with known di=%b do=%b", di, do);
    end

    // Coverage: output both values and all four OR-group combinations
    cover (do==1'b0);
    cover (do==1'b1);
    cover ({(di[1]|di[0]),(di[3]|di[2])}==2'b00);
    cover ({(di[1]|di[0]),(di[3]|di[2])}==2'b01);
    cover ({(di[1]|di[0]),(di[3]|di[2])}==2'b10);
    cover ({(di[1]|di[0]),(di[3]|di[2])}==2'b11);

    // Per-bit stimulus presence (seen 0 and 1 for each input bit)
    cover (!di[0]); cover (di[0]);
    cover (!di[1]); cover (di[1]);
    cover (!di[2]); cover (di[2]);
    cover (!di[3]); cover (di[3]);
  end
endmodule

bind top top_sva_chk i_top_sva_chk (.di(di), .do(do), .d(d));