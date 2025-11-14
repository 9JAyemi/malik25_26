// SVA for top_module, shift_register, and accu
// Focused, bound checkers with key assertions and covers

// ---------- top_module checker ----------
module top_sva (
  input clk, input rst_n,
  input [7:0] data_in, input [7:0] q,
  input [23:0] shift_out,
  input [9:0] accu_out,
  input [7:0] shift_in,
  input valid_a, input ready_a, input ready_b
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  a_top_reset: assert property (cb !rst_n |=> (shift_in==8'b0 && valid_a==1'b0 && ready_b==1'b0 && q==8'b0));

  // Registered assignments in top
  a_shiftin_din: assert property (cb rst_n && $past(rst_n) |-> shift_in == $past(data_in));
  a_q_tracks_accu: assert property (cb rst_n && $past(rst_n) |-> q == $past(accu_out[9:2]));
  a_ready_b_pipe: assert property (cb rst_n && $past(rst_n) |-> ready_b == $past(ready_a));

  // Handshake liveness (detects deadlock)
  a_no_deadlock: assert property (cb disable iff (!rst_n) valid_a |-> ##[1:32] ready_a);

  // Covers
  c_hs_seen: cover property (cb disable iff (!rst_n) (valid_a && ready_b));
  c_out_seen: cover property (cb disable iff (!rst_n) (ready_a && ready_b && valid_a)); // any successful handshake observed
endmodule

bind top_module top_sva i_top_sva (.*);

// ---------- shift_register checker ----------
module shift_register_sva (input clk, input [7:0] d, input [23:0] q);
  default clocking cb @(posedge clk); endclocking
  // Shift behavior: q(t) == {q(t-1)[15:0], d(t-1)}
  a_shift: assert property (cb
    (!$isunknown($past(q)) && !$isunknown($past(d))) |-> q == { $past(q[15:0]), $past(d) }
  );
  // Cover: observe any non-zero shift after having valid past
  c_shift_activity: cover property (cb (!$isunknown($past(q)) && !$isunknown($past(d))) ##1 (q != 24'h0));
endmodule

bind shift_register shift_register_sva i_shift_register_sva (.*);

// ---------- accu checker ----------
module accu_sva (
  input clk, input rst_n,
  input [7:0] data_in,
  input valid_a, input ready_b,
  input ready_a,
  input valid_b,
  input [9:0] data_out,
  input [31:0] accu_reg,
  input [1:0] count
);
  default clocking cb @(posedge clk); endclocking

  // Reset state
  a_accu_reset: assert property (cb !rst_n |=> (accu_reg==32'b0 && count==2'b0 && valid_b==1'b0));

  // Combinational ready_a definition
  a_ready_a_def: assert property (cb ready_a == (!valid_a || ready_b));

  // No handshake: hold state
  a_hold_no_hs: assert property (cb !(valid_a && ready_b) |=> (accu_reg == $past(accu_reg)
                                                              && count    == $past(count)
                                                              && valid_b  == $past(valid_b)
                                                              && data_out == $past(data_out)));

  // Handshake when count != 2: accumulate and increment, valid_b unchanged
  a_hs_norm: assert property (cb (valid_a && ready_b && (count != 2)) |=> (accu_reg == $past(accu_reg) + data_in
                                                                           && count   == $past(count) + 1
                                                                           && valid_b == $past(valid_b)));

  // Handshake when count == 2: output slice, shift-down, count reset, valid_b asserted
  a_hs_out: assert property (cb (valid_a && ready_b && (count == 2)) |=> (valid_b
                                                                          && data_out == $past(accu_reg[31:22])
                                                                          && accu_reg == $past(accu_reg[21:0])
                                                                          && count == 2'b00));

  // While valid_b is asserted and not producing a new output, data_out holds
  a_data_stable_while_valid: assert property (cb (valid_b && !(valid_a && ready_b && (count == 2))) |=> $stable(data_out));

  // Coverage: see 3 handshakes leading to an output event
  sequence s_hs; (valid_a && ready_b); endsequence
  c_three_hs_to_out: cover property (cb disable iff (!rst_n) s_hs[*3] ##1 valid_b);
endmodule

bind accu accu_sva i_accu_sva (.*);