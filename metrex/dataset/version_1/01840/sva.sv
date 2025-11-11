// SVA checker for premuat_8: concise, full functional checks + key coverage
module premuat_8_assert (
  input                enable,
  input                inverse,
  input  signed [27:0] i_0,
  input  signed [27:0] i_1,
  input  signed [27:0] i_2,
  input  signed [27:0] i_3,
  input  signed [27:0] i_4,
  input  signed [27:0] i_5,
  input  signed [27:0] i_6,
  input  signed [27:0] i_7,
  input  signed [27:0] o_0,
  input  signed [27:0] o_1,
  input  signed [27:0] o_2,
  input  signed [27:0] o_3,
  input  signed [27:0] o_4,
  input  signed [27:0] o_5,
  input  signed [27:0] o_6,
  input  signed [27:0] o_7
);

  // Functional correctness (combinational, immediate assertions)
  always_comb begin
    // Pass-through outs
    assert (o_0 == i_0) else $error("premuat_8: o_0 != i_0");
    assert (o_7 == i_7) else $error("premuat_8: o_7 != i_7");

    // Main muxing behavior
    if (!enable) begin
      assert (o_1 == i_1) else $error("premuat_8: !enable o_1 mismatch");
      assert (o_2 == i_2) else $error("premuat_8: !enable o_2 mismatch");
      assert (o_3 == i_3) else $error("premuat_8: !enable o_3 mismatch");
      assert (o_4 == i_4) else $error("premuat_8: !enable o_4 mismatch");
      assert (o_5 == i_5) else $error("premuat_8: !enable o_5 mismatch");
      assert (o_6 == i_6) else $error("premuat_8: !enable o_6 mismatch");
    end
    else if (inverse) begin
      assert (o_1 == i_2) else $error("premuat_8: inv o_1!=i_2");
      assert (o_2 == i_4) else $error("premuat_8: inv o_2!=i_4");
      assert (o_3 == i_6) else $error("premuat_8: inv o_3!=i_6");
      assert (o_4 == i_1) else $error("premuat_8: inv o_4!=i_1");
      assert (o_5 == i_3) else $error("premuat_8: inv o_5!=i_3");
      assert (o_6 == i_5) else $error("premuat_8: inv o_6!=i_5");
    end
    else begin
      assert (o_1 == i_4) else $error("premuat_8: fwd o_1!=i_4");
      assert (o_2 == i_1) else $error("premuat_8: fwd o_2!=i_1");
      assert (o_3 == i_5) else $error("premuat_8: fwd o_3!=i_5");
      assert (o_4 == i_2) else $error("premuat_8: fwd o_4!=i_2");
      assert (o_5 == i_6) else $error("premuat_8: fwd o_5!=i_6");
      assert (o_6 == i_3) else $error("premuat_8: fwd o_6!=i_3");
    end

    // X-propagation sanity: if all inputs/controls are known, outputs must be known
    if (!$isunknown({enable,inverse,i_0,i_1,i_2,i_3,i_4,i_5,i_6,i_7})) begin
      assert (!$isunknown({o_0,o_1,o_2,o_3,o_4,o_5,o_6,o_7}))
        else $error("premuat_8: outputs contain X/Z while inputs known");
    end
  end

  // Lightweight coverage (hits both branches and pass-through)
  always_comb begin
    cover (!enable);
    cover (enable && !inverse);
    cover (enable &&  inverse);

    cover (!enable &&
           o_1==i_1 && o_2==i_2 && o_3==i_3 && o_4==i_4 && o_5==i_5 && o_6==i_6);

    cover (enable && !inverse &&
           o_1==i_4 && o_2==i_1 && o_3==i_5 && o_4==i_2 && o_5==i_6 && o_6==i_3);

    cover (enable &&  inverse &&
           o_1==i_2 && o_2==i_4 && o_3==i_6 && o_4==i_1 && o_5==i_3 && o_6==i_5);
  end

endmodule

// Bind into DUT (no DUT/testbench code changes required)
bind premuat_8 premuat_8_assert u_premuat_8_assert (.*);