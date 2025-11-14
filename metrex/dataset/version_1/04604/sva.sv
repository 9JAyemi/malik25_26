// SVA for bcd_converter: checks correctness and provides concise coverage
// Uses $global_clock so no DUT clock is required.

module bcd_converter_sva (
  input logic [3:0] in,
  input logic [3:0] out,
  input logic       invalid
);

  default clocking @(posedge $global_clock); endclocking

  function automatic bit is_valid_bcd (logic [3:0] v);
    return (v <= 4'd9);
  endfunction

  // Valid inputs 0..9 must pass-through and invalid==0; outputs must be known
  property p_valid_maps;
    !$isunknown(in) && is_valid_bcd(in)
      |-> (!invalid && out==in && !$isunknown(out));
  endproperty
  assert property (p_valid_maps)
    else $error("bcd_converter: valid in (0..9) must map to out==in and invalid==0");

  // Invalid inputs 10..15 must assert invalid and drive Xs on out
  property p_invalid_maps;
    !$isunknown(in) && !is_valid_bcd(in)
      |-> (invalid && $isunknown(out));
  endproperty
  assert property (p_invalid_maps)
    else $error("bcd_converter: invalid in (10..15) must set invalid==1 and out to X");

  // Consistency: invalid may only be 1 for inputs 10..15
  property p_invalid_consistency;
    invalid |-> !is_valid_bcd(in);
  endproperty
  assert property (p_invalid_consistency)
    else $error("bcd_converter: invalid==1 only allowed when in is 10..15");

  // Out must be known whenever invalid==0
  property p_out_known_when_not_invalid;
    !invalid |-> !$isunknown(out);
  endproperty
  assert property (p_out_known_when_not_invalid)
    else $error("bcd_converter: out must be known when invalid==0");

  // Functional coverage: hit each valid code 0..9 with correct behavior
  genvar i;
  generate
    for (i=0; i<10; i++) begin : COV_VALID
      cover property (in==i[3:0] && !invalid && out==in);
    end
  endgenerate

  // Functional coverage: hit each invalid code 10..15 with invalid asserted
  cover property (in==4'd10 && invalid);
  cover property (in==4'd11 && invalid);
  cover property (in==4'd12 && invalid);
  cover property (in==4'd13 && invalid);
  cover property (in==4'd14 && invalid);
  cover property (in==4'd15 && invalid);

endmodule

// Bind into the DUT
bind bcd_converter bcd_converter_sva u_bcd_converter_sva(.in(in), .out(out), .invalid(invalid));