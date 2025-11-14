// SVA for odd_even. Bind this to the DUT.
module odd_even_sva (
  input [2:0] input_bits,
  input [1:0] output_bits
);

  default clocking cb @(input_bits or output_bits); endclocking

  // Functional correctness for resolved LSB
  assert property ( (input_bits[0] === 1'b1) |-> (output_bits == 2'b01) );
  assert property ( (input_bits[0] === 1'b0) |-> (output_bits == 2'b10) );

  // Output encoding legality and cleanliness
  assert property ( output_bits inside {2'b01, 2'b10} );
  assert property ( !$isunknown(output_bits) );

  // Upper bits must not affect output
  assert property ( ($changed(input_bits[2:1]) && $stable(input_bits[0])) |-> $stable(output_bits) );

  // Output changes only when LSB changes (after first sample)
  assert property ( (!$isunknown($past(output_bits))) |-> ($changed(output_bits) -> $changed(input_bits[0])) );

  // Coverage
  cover property ( input_bits[0] && (output_bits == 2'b01) );
  cover property ( !input_bits[0] && (output_bits == 2'b10) );
  cover property (@(input_bits) (!input_bits[0] && output_bits==2'b10) ##1 (input_bits[0] && output_bits==2'b01) );
  cover property (@(input_bits) ( input_bits[0] && output_bits==2'b01) ##1 (!input_bits[0] && output_bits==2'b10) );

endmodule

bind odd_even odd_even_sva odd_even_sva_i (.*);