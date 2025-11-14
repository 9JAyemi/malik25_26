// SVA for selector. Bind to all instances and check both structure and end-to-end function.
module selector_sva;

  // Sample on any input change; guard against X/Z on inputs
  localparam bit USE_GUARD = 1;

  // Helper functions
  function automatic bit no_x_inputs;
    return !$isunknown({pm0,pm1,pm2,pm3});
  endfunction

  // Output known when inputs known
  assert property (@(pm0 or pm1 or pm2 or pm3)
    (!USE_GUARD || no_x_inputs()) |-> !$isunknown({d0,d1})
  ) else $error("selector: outputs X/Z with known inputs");

  // d0 end-to-end functional check
  assert property (@(pm0 or pm1 or pm2 or pm3)
    (!USE_GUARD || no_x_inputs()) |->
      d0 === ( (~(pm0[0] | pm0[1]) & ~(pm0[2] | pm0[3]))
             | (~(pm1[0] | pm1[1]) & ~(pm1[2] | pm1[3])) )
  ) else $error("selector: d0 functional mismatch");

  // Structural checks for d0 path
  assert property (@(pm0 or pm1)
    (!USE_GUARD || no_x_inputs()) |->
      (n1 === ~(pm0[0] | pm0[1])) && (n2 === ~(pm0[2] | pm0[3])) &&
      (n3 === ~(pm1[0] | pm1[1])) && (n4 === ~(pm1[2] | pm1[3])) &&
      (n5 === (n1 & n2)) && (n6 === (n3 & n4)) &&
      (d0 === (n5 | n6))
  ) else $error("selector: d0 structural mismatch");

  // d1 end-to-end functional check
  assert property (@(pm0 or pm1 or pm2 or pm3)
    (!USE_GUARD || no_x_inputs()) |->
      d1 === (
        // OR of four 3-input NANDs across bit lanes
        ( ~(pm0[0] & pm1[0] & pm2[0])
        | ~(pm0[1] & pm1[1] & pm2[1])
        | ~(pm0[2] & pm1[2] & pm2[2])
        | ~(pm0[3] & pm1[3] & pm2[3]) )
        |
        // OR with inversion of (two 2x2 NAND-and-OR cones)
        ~ ( ( ~(pm2[0] & pm2[1]) & ~(pm2[2] & pm2[3]) )
          | ( ~(pm3[0] & pm3[1]) & ~(pm3[2] & pm3[3]) ) )
      )
  ) else $error("selector: d1 functional mismatch");

  // Structural checks for d1 path
  assert property (@(pm0 or pm1 or pm2 or pm3)
    (!USE_GUARD || no_x_inputs()) |->
      (n8  === ~(pm2[0] & pm2[1])) &&
      (n9  === ~(pm2[2] & pm2[3])) &&
      (n10 === ~(pm3[0] & pm3[1])) &&
      (n11 === ~(pm3[2] & pm3[3])) &&
      (n12 === (n8  & n9 )) &&
      (n13 === (n10 & n11)) &&
      (n14 === (n12 | n13)) &&
      (n15 === ~(pm0[0] & pm1[0] & pm2[0])) &&
      (n16 === ~(pm0[1] & pm1[1] & pm2[1])) &&
      (n17 === ~(pm0[2] & pm1[2] & pm2[2])) &&
      (n18 === ~(pm0[3] & pm1[3] & pm2[3])) &&
      (n19 === (n15 | n16)) &&
      (n20 === (n17 | n18)) &&
      (n21 === (n19 | n20)) &&
      (n22 === ~n14) &&
      (d1  === (n21 | n22))
  ) else $error("selector: d1 structural mismatch");

  // Minimal, high-value functional covers

  // d0: each OR-leg can independently drive 1, and 0 when both legs 0
  cover property (@(pm0 or pm1) (!USE_GUARD || no_x_inputs()) && (n5 && !n6) && (d0==1'b1));
  cover property (@(pm0 or pm1) (!USE_GUARD || no_x_inputs()) && (!n5 && n6) && (d0==1'b1));
  cover property (@(pm0 or pm1) (!USE_GUARD || no_x_inputs()) && (!n5 && !n6) && (d0==1'b0));

  // d1: exercise OR truth table of (n21, n22)
  cover property (@(pm0 or pm1 or pm2 or pm3) (!USE_GUARD || no_x_inputs()) && (n21==0 && n22==0) && (d1==0));
  cover property (@(pm0 or pm1 or pm2 or pm3) (!USE_GUARD || no_x_inputs()) && (n21==0 && n22==1) && (d1==1));
  cover property (@(pm0 or pm1 or pm2 or pm3) (!USE_GUARD || no_x_inputs()) && (n21==1 && n22==0) && (d1==1));
  cover property (@(pm0 or pm1 or pm2 or pm3) (!USE_GUARD || no_x_inputs()) && (n21==1 && n22==1) && (d1==1));

  // Corner covers
  // n14==0 => n22==1 path dominates
  cover property (@(pm0 or pm1 or pm2 or pm3) (!USE_GUARD || no_x_inputs()) && (n14==0) && (n22==1));
  // n21==0 (all bit-lane triples are 1)
  cover property (@(pm0 or pm1 or pm2 or pm3)
    (!USE_GUARD || no_x_inputs()) && (n21==0)
  );

endmodule

bind selector selector_sva u_selector_sva();