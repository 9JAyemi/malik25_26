// SVA checker for PP_NEW (binds to internal nets to verify structure and function)
module PP_NEW_sva (
  input  logic ONEPOS, ONENEG, TWOPOS, TWONEG,
  input  logic INA, INB, INC, IND,
  input  logic PPBIT,
  input  logic A, B, C, D, E
);
  // derived pair terms
  wire p0 = INA & TWOPOS;
  wire p1 = INB & TWONEG;
  wire p2 = INC & ONEPOS;
  wire p3 = IND & ONENEG;

  // structural and functional checks (4-state and 2-state forms)
  always_comb begin
    assert (A === ~p0) else $error("A mismatch");
    assert (B === ~p1) else $error("B mismatch");
    assert (C === ~p2) else $error("C mismatch");
    assert (D === ~p3) else $error("D mismatch");
    assert (E === (A & B & C & D)) else $error("E mismatch");
    assert (PPBIT === ~E) else $error("PPBIT vs E mismatch");
    assert (PPBIT === (p0 | p1 | p2 | p3)) else $error("PPBIT function mismatch");

    if (!$isunknown({INA,INB,INC,IND,ONEPOS,ONENEG,TWOPOS,TWONEG})) begin
      assert (PPBIT == (p0 | p1 | p2 | p3)) else $error("Resolved PPBIT mismatch");
      assert (!$isunknown(PPBIT)) else $error("PPBIT unknown with resolved inputs");
    end
  end

  // compact functional coverage
  always_comb begin
    cover (!p0 && !p1 && !p2 && !p3 && PPBIT==1'b0); // none -> 0
    cover ( p0 && !p1 && !p2 && !p3 && PPBIT==1'b1); // single pair -> 1
    cover (!p0 &&  p1 && !p2 && !p3 && PPBIT==1'b1);
    cover (!p0 && !p1 &&  p2 && !p3 && PPBIT==1'b1);
    cover (!p0 && !p1 && !p2 &&  p3 && PPBIT==1'b1);
    cover ((p0+p1+p2+p3)>=2 && PPBIT==1'b1);         // any 2+ pairs -> 1
    cover ( p0 && p1 && p2 && p3 && PPBIT==1'b1);     // all four -> 1
  end
endmodule

bind PP_NEW PP_NEW_sva u_pp_new_sva (.*);