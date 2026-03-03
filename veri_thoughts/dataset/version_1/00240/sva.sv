// SVA for sequential_circuit
// Bind with: bind sequential_circuit sequential_circuit_sva sva();

module sequential_circuit_sva (sequential_circuit dut);

  default clocking cb @(posedge dut.clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge dut.clk) past_valid <= 1'b1;

  default disable iff (!past_valid);

  // Functional correctness
  a_reset_dominates: assert property (dut.b |=> dut.counter == 2'd0);
  a_inc:             assert property ((!dut.b && dut.a) |=> dut.counter == $past(dut.counter) + 2'd1);
  a_hold:            assert property ((!dut.b && !dut.a) |=> dut.counter == $past(dut.counter));
  a_reset_over_inc:  assert property ((dut.a && dut.b) |=> dut.counter == 2'd0);
  a_q_alias:         assert property (dut.q == dut.counter);
  a_ff_capture:      assert property (dut.flip_flop == $past(dut.counter[1]));

  // Change only when expected
  a_change_caused:   assert property (
                       (dut.counter != $past(dut.counter))
                       |-> ($past(dut.b) || (!$past(dut.b) && $past(dut.a)))
                     );

  // Coverage
  c_inc:                    cover property (!dut.b && dut.a);
  c_hold:                   cover property (!dut.b && !dut.a);
  c_b_only:                 cover property ( dut.b && !dut.a);
  c_a_and_b:                cover property ( dut.a &&  dut.b);
  c_wrap:                   cover property (($past(dut.counter)==2'd3 && !dut.b && dut.a) |=> dut.counter==2'd0);
  c_reset_from_nonzero:     cover property (($past(dut.counter)!=2'd0 && dut.b)         |=> dut.counter==2'd0);
  c_ff_rose:                cover property ($rose(dut.flip_flop));
  c_ff_fell:                cover property ($fell(dut.flip_flop));

endmodule