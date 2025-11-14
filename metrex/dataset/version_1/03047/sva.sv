// SVA for crossbar — bindable, clockless, concise, full functional checks + coverage

module crossbar_sva;
  // Immediate assertions cover combinational behavior on any input change
  always_comb begin
    // Functional correctness (actual behavior given width truncation)
    assert (out1 == (sel2[0] ? in4 : in3))
      else $error("crossbar: out1 mismatch exp=%0h got=%0h sel2[0]=%0b in3=%0h in4=%0h",
                  (sel2[0] ? in4 : in3), out1, sel2[0], in3, in4);
    assert (out2 == (sel2[0] ? in3 : in4))
      else $error("crossbar: out2 mismatch exp=%0h got=%0h sel2[0]=%0b in3=%0h in4=%0h",
                  (sel2[0] ? in3 : in4), out2, sel2[0], in3, in4);
    assert (out3 == (sel2[1] ? in4 : in3))
      else $error("crossbar: out3 mismatch exp=%0h got=%0h sel2[1]=%0b in3=%0h in4=%0h",
                  (sel2[1] ? in4 : in3), out3, sel2[1], in3, in4);
    assert (out4 == (sel2[1] ? in3 : in4))
      else $error("crossbar: out4 mismatch exp=%0h got=%0h sel2[1]=%0b in3=%0h in4=%0h",
                  (sel2[1] ? in3 : in4), out4, sel2[1], in3, in4);

    // Pair permutation sanity (out1/out2 are {in3,in4} in some order; same for out3/out4)
    assert ( ((out1==in3)&&(out2==in4)) || ((out1==in4)&&(out2==in3)) )
      else $error("crossbar: (out1,out2) not a permutation of (in3,in4)");
    assert ( ((out3==in3)&&(out4==in4)) || ((out3==in4)&&(out4==in3)) )
      else $error("crossbar: (out3,out4) not a permutation of (in3,in4)");

    // No X/Z on outputs when driving inputs/selects are known
    if (!$isunknown({in3,in4,sel2[0]})) begin
      assert (!$isunknown(out1)) else $error("crossbar: out1 X/Z with known inputs");
      assert (!$isunknown(out2)) else $error("crossbar: out2 X/Z with known inputs");
    end
    if (!$isunknown({in3,in4,sel2[1]})) begin
      assert (!$isunknown(out3)) else $error("crossbar: out3 X/Z with known inputs");
      assert (!$isunknown(out4)) else $error("crossbar: out4 X/Z with known inputs");
    end

    // Coverage: exercise both selections per bit and all sel2 combinations
    cover (sel2[0]==0 && out1==in3 && out2==in4);
    cover (sel2[0]==1 && out1==in4 && out2==in3);
    cover (sel2[1]==0 && out3==in3 && out4==in4);
    cover (sel2[1]==1 && out3==in4 && out4==in3);
    cover (sel2==2'b00);
    cover (sel2==2'b01);
    cover (sel2==2'b10);
    cover (sel2==2'b11);
  end
endmodule

bind crossbar crossbar_sva;