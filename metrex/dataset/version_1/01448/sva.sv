// SVA for four_bit_adder
module four_bit_adder_sva(
  input logic [3:0] a, b,
  input logic       enable,
  input logic [3:0] sum
);
  default clocking cb @(a or b or enable or sum); endclocking

  // Functional correctness
  assert property ( enable && !$isunknown({a,b})
                    |-> ##0 sum == ({1'b0,a}+{1'b0,b})[3:0] );
  assert property ( !enable |-> ##0 sum == 4'h0 );

  // No X on output when inputs known
  assert property ( !$isunknown({a,b,enable}) |-> ##0 !$isunknown(sum) );

  // No spurious output change without input change
  assert property ( $changed(sum) |-> ($changed(a) || $changed(b) || $changed(enable)) );

  // Coverage
  cover property ( enable );                         // enabled case seen
  cover property ( !enable );                        // disabled case seen
  cover property ( enable && !(({1'b0,a}+{1'b0,b})[4]) ); // no overflow
  cover property ( enable &&  (({1'b0,a}+{1'b0,b})[4]) ); // overflow/wrap
  cover property ( enable && sum==4'h0 && (|a || |b) );   // wrap to zero
  cover property ( enable && a==4'h0 && b==4'h0 );
  cover property ( enable && a==4'hF && b==4'hF );
endmodule

bind four_bit_adder four_bit_adder_sva sva_inst (.*);