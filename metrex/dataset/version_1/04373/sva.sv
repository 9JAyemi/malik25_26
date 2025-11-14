// SVA checker for mux2; bind to DUT for use
module mux2_sva #(parameter bitwidth=32)
  (input logic sel,
   input logic [bitwidth-1:0] a, b, y);

  // Static sanity
  initial assert ($bits(a)==bitwidth && $bits(b)==bitwidth && $bits(y)==bitwidth);

  // Core functional check and key properties/coverage
  always_comb begin
    // Functional equivalence (4-state consistent)
    assert (y === (sel ? b : a))
      else $error("mux2 func mismatch: sel=%0b a=%0h b=%0h y=%0h", sel, a, b, y);

    // If inputs are known, output must be known
    if (!$isunknown({sel,a,b})) begin
      assert (!$isunknown(y)) else $error("mux2 unexpected X/Z on y with known inputs");
    end

    // Non-selected input must not affect y
    if (!sel && $changed(b) && $stable(a)) assert ($stable(y))
      else if ( sel && $changed(a) && $stable(b)) assert ($stable(y));

    // Selected input change must reflect on y immediately
    if (!sel && $changed(a)) assert ($changed(y) && y===a)
      else if ( sel && $changed(b)) assert ($changed(y) && y===b);

    // Select change effect
    if ($changed(sel)) begin
      assert (y === (sel ? b : a));
      if (a != b) assert ($changed(y));
    end

    // Coverage: both paths, select toggle effects, selected/non-selected data changes
    cover (sel==0 && y===a);
    cover (sel==1 && y===b);
    cover ($changed(sel) && (a!=b) && $changed(y));
    cover (!sel && $changed(a) && $changed(y));
    cover ( sel && $changed(b) && $changed(y));
    cover (!sel && $changed(b) && $stable(y));
    cover ( sel && $changed(a) && $stable(y));
  end
endmodule

bind mux2 mux2_sva #(.bitwidth(bitwidth)) mux2_sva_i (.sel(sel), .a(a), .b(b), .y(y));