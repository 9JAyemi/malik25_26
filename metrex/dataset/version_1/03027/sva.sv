// SVA for module accu. Bind this after compiling DUT.

module accu_sva;

  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset state checks (immediate on sampled clock)
  always @(posedge clk) if (!rst_n) begin
    assert (acc_reg   == 8'b0);
    assert (count_reg == 3'b0);
    assert (pipe_reg  == 10'b0);
    assert (valid_b   == 1'b0);
    assert (data_out  == 10'b0);
  end

  // Functional checks (disabled during reset)
  default disable iff (!rst_n);

  // Combinational spec for ready_a
  a_readya:    assert property (ready_a == (~valid_b & ready_b));

  // Next-state of accumulator and counter
  a_acc_next:  assert property (acc_reg ==
                                ($past(valid_a) ? ($past(acc_reg) + $past(data_in)) : $past(acc_reg)));

  a_cnt_next:  assert property (count_reg ==
                                ($past(valid_a)
                                   ? (($past(count_reg)==3'b111) ? 3'b000 : $past(count_reg)+3'b001)
                                   : $past(count_reg)));

  // Next-state of pipe_reg (note truncation follows RTL semantics)
  a_pipe_next: assert property (pipe_reg ==
                                ($past(count_reg)==3'b111
                                   ? {2'b00,                $past(acc_reg)}
                                   : {$past(pipe_reg[7:0]), $past(acc_reg)}));

  // Output timing relationships (driven by previous cycle state)
  a_vldb:      assert property (valid_b  == ($past(count_reg)==3'b111));
  a_dout:      assert property (data_out == (($past(count_reg)==3'b111) ? $past(pipe_reg) : 10'b0));

  // Stability when no input valid (explicit)
  a_hold_no_va: assert property (!$past(valid_a) |-> (acc_reg==$past(acc_reg) && count_reg==$past(count_reg)));

  // If we advanced but did not hit terminal count last cycle, valid_b must be 0 this cycle
  a_no_vldb_mid: assert property ($past(valid_a) && ($past(count_reg)!=3'b111) |-> !valid_b);

  // Coverage
  c_reset_deassert: cover property ($rose(rst_n));
  c_8in_1out:       cover property (valid_a[*8] ##1 valid_b);
  c_wrap_event:     cover property ($past(count_reg)==3'b111 ##1 (valid_b && data_out==$past(pipe_reg)));
  c_pipe_load:      cover property ($past(count_reg)==3'b111 ##1 pipe_reg=={2'b00, $past(acc_reg)});
  c_backpressure:   cover property (ready_b && valid_b && !ready_a);
  c_sticky_vldb:    cover property (valid_b && !valid_a ##1 valid_b && !valid_a);

endmodule

bind accu accu_sva accu_sva_i();