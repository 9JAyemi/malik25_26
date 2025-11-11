// SVA for or4b: X must be ~(A|B|C|D_N). Includes correctness, X/unknown checks, and concise coverage.
// Bind this file alongside the DUT.

module or4b_sva (input logic A, B, C, D_N, X);

  // Immediate assertion in comb region (fast, catches same-delta mismatches)
  always_comb begin
    assert (X === ~(A | B | C | D_N))
      else $error("or4b func mismatch: X=%b, exp=%b for A=%b B=%b C=%b D_N=%b",
                  X, ~(A|B|C|D_N), A, B, C, D_N);
  end

  // Concurrent assertions with event-based sampling; ##0 to avoid race with continuous assigns
  default clocking cb @ (A or B or C or D_N); endclocking

  // Functional equivalence
  assert property (##0 (X === ~(A | B | C | D_N)))
    else $error("or4b func mismatch (concurrent)");

  // If any input is known 1, output must be 0 (4-state safe)
  assert property ( (A===1 || B===1 || C===1 || D_N===1) |-> ##0 (X===0) )
    else $error("or4b: any-1 did not force X=0");

  // If all inputs are known 0, output must be 1
  assert property ( (A===0 && B===0 && C===0 && D_N===0) |-> ##0 (X===1) )
    else $error("or4b: all-0 did not force X=1");

  // Known-in implies known-out
  assert property ( !$isunknown({A,B,C,D_N}) |-> ##0 !$isunknown(X) )
    else $error("or4b: X unknown with known inputs");

  // Minimal but effective toggle-response coverage
  // Rising any single input from 0 with others 0 should drive X low
  cover property (@(posedge A) (B==0 && C==0 && D_N==0) ##0 (X==0));
  cover property (@(posedge B) (A==0 && C==0 && D_N==0) ##0 (X==0));
  cover property (@(posedge C) (A==0 && B==0 && D_N==0) ##0 (X==0));
  cover property (@(posedge D_N) (A==0 && B==0 && C==0) ##0 (X==0));

  // Falling the last asserted input should release X high
  cover property (@(negedge A) (B==0 && C==0 && D_N==0) ##0 (X==1));
  cover property (@(negedge B) (A==0 && C==0 && D_N==0) ##0 (X==1));
  cover property (@(negedge C) (A==0 && B==0 && D_N==0) ##0 (X==1));
  cover property (@(negedge D_N) (A==0 && B==0 && C==0) ##0 (X==1));

  // Full 16-vector functional coverage (compact)
  // Samples on any input change; ignores unknown inputs
  covergroup cg_inputs @(A or B or C or D_N);
    cp_inputs: coverpoint {A,B,C,D_N} iff (!$isunknown({A,B,C,D_N})) {
      bins all[] = {[0:15]};
    }
    cp_x: coverpoint X iff (!$isunknown({A,B,C,D_N}));
  endgroup
  cg_inputs cg = new();

endmodule

bind or4b or4b_sva i_or4b_sva (.*);