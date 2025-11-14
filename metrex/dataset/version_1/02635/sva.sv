// SVA for sky130_fd_sc_ms__a21bo
// Function: X = (A1 & A2) | ~B1_N

module sky130_fd_sc_ms__a21bo_sva (input logic A1, A2, B1_N, X);
  default clocking cb @(*); endclocking

  function logic f_ref(input logic a1, a2, b1n);
    return (a1 & a2) | ~b1n;
  endfunction

  // Functional equivalence when inputs are known
  ap_func:      assert property (!$isunknown({A1,A2,B1_N}) |-> (X == f_ref(A1,A2,B1_N)))
                 else $error("a21bo func mismatch");

  // Zero-delay combinational settle (same delta)
  ap_zerodelay: assert property (!$isunknown({A1,A2,B1_N}) |-> ##0 (X == f_ref(A1,A2,B1_N)))
                 else $error("a21bo zero-delay mismatch");

  // Basic sanity
  ap_no_z:      assert property (X !== 1'bz) else $error("a21bo X is Z");

  // Controlling value implications (robust to Xs on other inputs)
  ap_b0_forces1: assert property (B1_N === 1'b0 |-> X === 1'b1) else $error("B1_N=0 must force X=1");
  ap_and11_forces1: assert property ((A1 === 1'b1 && A2 === 1'b1) |-> X === 1'b1) else $error("A1=A2=1 must force X=1");
  ap_b1_and_zero_forces0: assert property ((B1_N === 1'b1 && (A1 === 1'b0 || A2 === 1'b0)) |-> X === 1'b0)
                           else $error("B1_N=1 and (A1=0||A2=0) must force X=0");

  // Coverage: all input combinations
  cover property (A1==0 && A2==0 && B1_N==0);
  cover property (A1==0 && A2==0 && B1_N==1);
  cover property (A1==0 && A2==1 && B1_N==0);
  cover property (A1==0 && A2==1 && B1_N==1);
  cover property (A1==1 && A2==0 && B1_N==0);
  cover property (A1==1 && A2==0 && B1_N==1);
  cover property (A1==1 && A2==1 && B1_N==0);
  cover property (A1==1 && A2==1 && B1_N==1);

  // Coverage: output values and key implications observed
  cover property (X==0);
  cover property (X==1);
  cover property (B1_N===0 && X===1);
  cover property (A1===1 && A2===1 && X===1);
  cover property (B1_N===1 && (A1===0||A2===0) && X===0);
endmodule

bind sky130_fd_sc_ms__a21bo sky130_fd_sc_ms__a21bo_sva u_sva (.*);