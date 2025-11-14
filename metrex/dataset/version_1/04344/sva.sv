// SVA for accu: bind this to the DUT instance
module accu_sva;
  // These names refer to accu’s signals in the bound scope
  // clk, rst_n, data_in, valid_a, ready_b, ready_a, valid_b, data_out
  // internal: data_reg, count_reg

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // handy handshake
  sequence H; valid_a && ready_b; endsequence

  // Reset values hold while reset is asserted
  assert property (!rst_n |-> (data_reg==8'h00 && count_reg==4'h0 && valid_b==1'b0 && data_out==10'h000));

  // Ready/valid relation
  assert property (ready_a == ~valid_b);

  // Count range invariant (reachable states)
  assert property (count_reg inside {[4'd0:4'd8]});

  // No state change without handshake
  assert property (!H |=> $stable({data_reg, count_reg, valid_b, data_out}));

  // Accumulator updates on handshake
  assert property (H |-> data_reg == (($past(data_reg) + data_in) & 8'hFF));

  // Normal count increment when not at threshold; outputs unchanged
  assert property (H && $past(count_reg)!=4'd8 |-> (count_reg == $past(count_reg)+1
                                                   && valid_b == $past(valid_b)
                                                   && data_out == $past(data_out)));

  // Fire condition: when previous count==8 and handshake now
  assert property (H && $past(count_reg)==4'd8 |-> (valid_b && count_reg==4'd0
                                                   && data_out == {2'b00, $past(data_reg)}));

  // valid_b can only rise due to the fire condition
  assert property ($rose(valid_b) |-> (H && $past(count_reg)==4'd8));

  // data_out MSBs are always zero (by construction)
  assert property (data_out[9:8] == 2'b00);

  // Coverage
  cover property ($rose(valid_b));                               // ever fires
  cover property (H[*9] ##0 $rose(valid_b) && count_reg==4'd0);  // 9th handshake triggers fire
  cover property (!rst_n ##1 rst_n ##1 H[*9] ##0 $rose(valid_b)); // after reset, reach a fire
endmodule

bind accu accu_sva sva_accu_i();