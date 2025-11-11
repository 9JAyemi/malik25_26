// SVA bind module for xor4
module xor4_sva (
  input logic a, b, c, d,
  input logic out,
  input logic xor1_out, xor2_out,
  input logic VPWR, VGND, VPB, VNB
);

  // Sample on any input toggle; ##0 moves checks to observed region
  default clocking cb @(
    posedge a or negedge a or
    posedge b or negedge b or
    posedge c or negedge c or
    posedge d or negedge d
  ); endclocking

  // Functional equivalence (4-input parity)
  assert property (##0 (out == (a ^ b ^ c ^ d)))
    else $error("xor4 functional mismatch: out != a^b^c^d");

  // Structural decomposition checks
  assert property (##0 (xor1_out == (a ^ b)))
    else $error("xor1_out mismatch: xor1_out != a^b");
  assert property (##0 (xor2_out == (c ^ d ^ xor1_out)))
    else $error("xor2_out mismatch: xor2_out != c^d^xor1_out");
  assert property (##0 (out == xor2_out))
    else $error("out mismatch: out != xor2_out");

  // X-propagation hygiene: known inputs imply known internal/outputs
  assert property ((!$isunknown({a,b,c,d})) |-> ##0 (!$isunknown({xor1_out,xor2_out,out})))
    else $error("X detected on outputs with known inputs");

  // Parity change behavior: odd number of input changes toggles out
  assert property ( ($countones({$changed(a),$changed(b),$changed(c),$changed(d)}) % 2 == 1)
                    |-> ##0 (out != $past(out)) )
    else $error("Parity toggle rule violated (odd input changes)");

  // Even number of simultaneous input changes keeps out unchanged (when any changed)
  assert property ( ($countones({$changed(a),$changed(b),$changed(c),$changed(d)}) > 0) &&
                    ($countones({$changed(a),$changed(b),$changed(c),$changed(d)}) % 2 == 0)
                    |-> ##0 (out == $past(out)) )
    else $error("Parity hold rule violated (even input changes)");

  // Basic coverage
  cover property (##0 out == 1'b0);
  cover property (##0 out == 1'b1);
  cover property (@(posedge a) 1);
  cover property (@(negedge a) 1);
  cover property (@(posedge b) 1);
  cover property (@(negedge b) 1);
  cover property (@(posedge c) 1);
  cover property (@(negedge c) 1);
  cover property (@(posedge d) 1);
  cover property (@(negedge d) 1);

  // Parity change coverage (1/2/3/4 simultaneous input changes)
  cover property ( ($countones({$changed(a),$changed(b),$changed(c),$changed(d)}) == 1) ##0 (out != $past(out)) );
  cover property ( ($countones({$changed(a),$changed(b),$changed(c),$changed(d)}) == 2) ##0 (out == $past(out)) );
  cover property ( ($countones({$changed(a),$changed(b),$changed(c),$changed(d)}) == 3) ##0 (out != $past(out)) );
  cover property ( ($countones({$changed(a),$changed(b),$changed(c),$changed(d)}) == 4) ##0 (out == $past(out)) );

  // Power/ground rails sanity (checked at time 0)
  initial begin
    assert (VPWR === 1'b1 && VPB === 1'b1 && VGND === 1'b0 && VNB === 1'b0)
      else $error("Power/ground rails incorrect");
  end

endmodule

// Bind into DUT, including internal nets
bind xor4 xor4_sva i_xor4_sva (
  .a(a), .b(b), .c(c), .d(d),
  .out(out),
  .xor1_out(xor1_out),
  .xor2_out(xor2_out),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);