// SVA for up_down_counter
module up_down_counter_sva (input clk, input up_down, input [3:0] count);
  default clocking cb @(posedge clk); endclocking

  // One-step modulo-16 behavior
  a_step_mod16: assert property (
    !$isunknown({$past(count), $past(up_down), count})
      |-> count == ($past(count) + ($past(up_down) ? 4'd1 : 4'd15))
  );

  // Coverage
  c_inc:       cover property (!$isunknown({$past(count),$past(up_down),count}) &&  $past(up_down) && count == ($past(count)+4'd1));
  c_dec:       cover property (!$isunknown({$past(count),$past(up_down),count}) && !$past(up_down) && count == ($past(count)+4'd15));
  c_wrap_up:   cover property (!$isunknown({$past(count),$past(up_down),count}) &&  $past(up_down) && ($past(count)==4'hF) && (count==4'h0));
  c_wrap_down: cover property (!$isunknown({$past(count),$past(up_down),count}) && !$past(up_down) && ($past(count)==4'h0) && (count==4'hF));
endmodule

bind up_down_counter up_down_counter_sva up_down_counter_sva_b (.*);

// SVA for shift_and_sum (top-level composition)
module shift_and_sum_sva (
  input [3:0] A, B,
  input       clk, up_down,
  input [7:0] out,
  input [3:0] counter1_out, counter2_out, binary_adder_out
);
  default clocking cb @(posedge clk); endclocking

  // Low nibble equals adder output and equals truncated sum of counters
  a_lo_sum_and_wiring: assert property (
    !$isunknown({counter1_out,counter2_out,binary_adder_out,out})
      |-> (out[3:0] == binary_adder_out && binary_adder_out == (counter1_out + counter2_out)[3:0])
  );

  // High nibble equals logical right shift of A by B
  a_hi_shift: assert property (
    !$isunknown({A,B,out}) |-> out[7:4] == (A >> B)
  );

  // Coverage
  c_adder_carry: cover property (
    !$isunknown({counter1_out,counter2_out}) &&
    (({1'b0,counter1_out} + {1'b0,counter2_out})[4] == 1'b1) // carry out
  );
  c_shift_by_0:  cover property (!$isunknown({A,B,out}) && (B==4'd0) && out[7:4]==A);
  c_shift_big:   cover property (!$isunknown({A,B,out}) && (B>=4'd4) && out[7:4]==4'd0);

  // Both counters wrap in the same cycle
  c_both_wrap_up: cover property (
    !$isunknown({$past(counter1_out),$past(counter2_out),$past(up_down),counter1_out,counter2_out}) &&
    $past(up_down) && $past(counter1_out)==4'hF && $past(counter2_out)==4'hF &&
    counter1_out==4'h0 && counter2_out==4'h0
  );
  c_both_wrap_down: cover property (
    !$isunknown({$past(counter1_out),$past(counter2_out),$past(up_down),counter1_out,counter2_out}) &&
    !$past(up_down) && $past(counter1_out)==4'h0 && $past(counter2_out)==4'h0 &&
    counter1_out==4'hF && counter2_out==4'hF
  );
endmodule

bind shift_and_sum shift_and_sum_sva shift_and_sum_sva_b (.*);