// SVA for sky130_fd_sc_hdll__a21oi: Y = ~ (B1 | (A1 & A2))
module sky130_fd_sc_hdll__a21oi_sva;
  // Immediate functional checks (robust to X/Z)
  always_comb begin
    if (!$isunknown({A1,A2,B1})) begin
      assert (Y === ~(B1 | (A1 & A2)))
        else $error("a21oi func mismatch: Y=%b A1=%b A2=%b B1=%b", Y, A1, A2, B1);
      assert (!$isunknown(Y))
        else $error("a21oi: Y is X/Z with known inputs");
    end
    // X-robust implications
    if (B1 === 1'b1)                          assert (Y === 1'b0) else $error("a21oi: B1=1 => Y=0");
    if (B1 === 1'b0 && A1 === 1'b1 && A2 === 1'b1) assert (Y === 1'b0) else $error("a21oi: B1=0,A1=A2=1 => Y=0");
    if (B1 === 1'b0 && A1 === 1'b0)           assert (Y === 1'b1) else $error("a21oi: B1=0,A1=0 => Y=1");
    if (B1 === 1'b0 && A2 === 1'b0)           assert (Y === 1'b1) else $error("a21oi: B1=0,A2=0 => Y=1");
    if (Y  === 1'b1)                          assert (B1 === 1'b0 && (A1 === 1'b0 || A2 === 1'b0))
                                               else $error("a21oi: Y=1 implies B1=0 and (A1=0 or A2=0)");
    if (Y  === 1'b0)                          assert (B1 === 1'b1 || (A1 === 1'b1 && A2 === 1'b1))
                                               else $error("a21oi: Y=0 implies B1=1 or (A1=A2=1)");
  end

  // Functional coverage of all input combinations (with expected Y)
  // Trigger on any 0/1 transition of inputs
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  (! $isunknown({A1,A2,B1})) && ({A1,A2,B1}==3'b000) && (Y===1));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  (! $isunknown({A1,A2,B1})) && ({A1,A2,B1}==3'b001) && (Y===0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  (! $isunknown({A1,A2,B1})) && ({A1,A2,B1}==3'b010) && (Y===1));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  (! $isunknown({A1,A2,B1})) && ({A1,A2,B1}==3'b011) && (Y===0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  (! $isunknown({A1,A2,B1})) && ({A1,A2,B1}==3'b100) && (Y===1));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  (! $isunknown({A1,A2,B1})) && ({A1,A2,B1}==3'b101) && (Y===0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  (! $isunknown({A1,A2,B1})) && ({A1,A2,B1}==3'b110) && (Y===0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  (! $isunknown({A1,A2,B1})) && ({A1,A2,B1}==3'b111) && (Y===0));

  // Y toggle coverage
  cover property (@(posedge Y) 1'b1);
  cover property (@(negedge Y) 1'b1);
endmodule

bind sky130_fd_sc_hdll__a21oi sky130_fd_sc_hdll__a21oi_sva a21oi_sva_i();