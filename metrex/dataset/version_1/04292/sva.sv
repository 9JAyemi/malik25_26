// SVA checker for ECC: bind into DUT and verify combinational relations and X/Z hygiene
module ECC_sva #(parameter int n = 8, p = 256, a = 1, b = 2) ();

  // Parameter sanity (elaboration-time)
  initial begin
    assert (n > 0) else $error("ECC: n must be > 0");
    assert (p > 2) else $error("ECC: p must be > 2");
  end

  // X/Z checks on interface
  always_comb begin
    assert (!$isunknown({P,A,B,Px,Py,Qx,Qy})) else $error("ECC: Inputs contain X/Z");
    assert (!$isunknown({Rx,Ry,Sx,Sy}))       else $error("ECC: Outputs contain X/Z");
  end

  // Internal structural/functional equivalence checks
  always_comb begin
    // constant point wiring
    assert (x1 == P_x) else $error("ECC: x1 != P_x");
    assert (y1 == P_y) else $error("ECC: y1 != P_y");
    assert (x2 == Q_x) else $error("ECC: x2 != Q_x");
    assert (y2 == Q_y) else $error("ECC: y2 != Q_y");

    // add path
    assert (x1x2 == (x1 + x2)) else $error("ECC: x1x2 mismatch");
    assert (m    == ((y2 - y1) * ((x2 - x1x2) ^ (p-2)))) else $error("ECC: m mismatch");
    assert (m2   == (m ^ 2)) else $error("ECC: m2 mismatch");
    assert (x3   == (m2 - x1x2 - a)) else $error("ECC: x3 mismatch");
    assert (x3x1 == (x3 - x1)) else $error("ECC: x3x1 mismatch");
    assert (y3   == (m * x1x2 - m * x3 - y1)) else $error("ECC: y3 mismatch");
    assert (y3y1 == (y3 - y1)) else $error("ECC: y3y1 mismatch");

    // outputs for R
    assert (Rx == x3) else $error("ECC: Rx mismatch");
    assert (Ry == y3) else $error("ECC: Ry mismatch");

    // sub path
    assert (Qx_neg == Qx) else $error("ECC: Qx_neg mismatch");
    assert (Qy_neg == (~Qy + 1)) else $error("ECC: Qy_neg mismatch");
    assert (Sx == (x1 + Qx_neg)) else $error("ECC: Sx mismatch");
    assert (Sy == (y1 + Qy_neg)) else $error("ECC: Sy mismatch");
  end

  // Basic functional/activation coverage
  cover property (x1x2 != 0);
  cover property (m    != 0);
  cover property (m2   != 0);
  cover property (Qy_neg != 0);
  cover property (Rx != Sx || Ry != Sy);
  cover property (Sy == (y1 - Qy)); // exercise two's-complement subtraction form

endmodule

// Bind the checker into all ECC instances
bind ECC ECC_sva #(.n(n), .p(p), .a(a), .b(b)) ECC_sva_i();