// SVA for v78e0a3_v9a2a06
// Bindable, concise, checks key combinational relationships and covers both branches.

module v78e0a3_v9a2a06_sva (
  input  logic [0:31] o,
  input  logic [0:31] i0,
  input  logic [0:7]  i1,
  input  logic [0:7]  i2,
  input  logic [0:7]  i3,
  input  logic [0:7]  i4
);

  // Mirror DUT combinational functions
  logic [0:31] concatenated_input_m;
  logic [0:31] subtracted_value_m;
  logic [0:31] inverted_subtracted_value_m;
  logic [0:31] add_one_m;
  logic [0:31] expected_o_m;

  assign concatenated_input_m        = {i1, i2, i3, i4};
  assign subtracted_value_m          = i0 - concatenated_input_m;
  assign inverted_subtracted_value_m = ~subtracted_value_m;
  assign add_one_m                   = {1'b1, {30{1'b0}}, 1'b0};
  assign expected_o_m                = (subtracted_value_m >= 0)
                                       ? subtracted_value_m
                                       : (inverted_subtracted_value_m + add_one_m);

  // Immediate assertions (combinational)
  always_comb begin
    // Output matches spec'd ternary
    assert (o === expected_o_m)
      else $error("o mismatch: o=%0h expected=%0h", o, expected_o_m);

    // Basic internal functional relations
    assert (concatenated_input_m === {i1,i2,i3,i4})
      else $error("concat mismatch");
    assert (inverted_subtracted_value_m === ~subtracted_value_m)
      else $error("invert mismatch");
    assert (add_one_m === {1'b1,{30{1'b0}},1'b0})
      else $error("add_one constant mismatch");

    // Byte-lane placement sanity (bit ordering [0:31])
    assert (concatenated_input_m[0 +: 8]  === i1) else $error("i1 lane mismatch");
    assert (concatenated_input_m[8 +: 8]  === i2) else $error("i2 lane mismatch");
    assert (concatenated_input_m[16 +: 8] === i3) else $error("i3 lane mismatch");
    assert (concatenated_input_m[24 +: 8] === i4) else $error("i4 lane mismatch");
  end

  // Clockless concurrent properties using $global_clock
  default clocking cb @($global_clock); endclocking

  // X-prop guard: if inputs are known, output must be known
  assert property ( !$isunknown({i0,i1,i2,i3,i4}) |-> !$isunknown(o) )
    else $error("X/Z propagated to o from known inputs");

  // Combinational stability: when inputs stable, o stable
  assert property ( $stable({i0,i1,i2,i3,i4}) |-> $stable(o) )
    else $error("o changed without input change");

  // Branch coverage
  cover property ( o === subtracted_value_m ); // then-branch
  cover property ( o === (inverted_subtracted_value_m + add_one_m) ); // else-branch (may be unreachable)

  // Value corner cases
  cover property ( subtracted_value_m == '0 );
  cover property ( !$isunknown({i0,i1,i2,i3,i4,o}) );

endmodule

bind v78e0a3_v9a2a06 v78e0a3_v9a2a06_sva sva (.*);