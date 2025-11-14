// SVA bind module for top_module
module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic        a,
  input logic        b,
  input logic        out_comb,
  input logic [3:0]  counter,
  input logic        even,
  input logic        odd,
  input logic        xor_out
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior (asynchronous assert, synchronous hold)
  ap_rst_async: assert property (@(posedge reset) ##0 counter == 4'h0);
  ap_rst_hold:  assert property (reset |-> counter == 4'h0);

  // Counter next-state behavior
  ap_cnt_after_reset_release: assert property (disable iff (reset)
                                               $past(reset) |-> counter == 4'h1);
  ap_cnt_inc: assert property (disable iff (reset)
                               !$past(reset) |-> ( ($past(counter) != 4'hF)
                                 ? counter == $past(counter)+1
                                 : counter == 4'h0 ));

  // Parity flags correctness
  ap_odd_def:   assert property (odd  == counter[0]);
  ap_even_def:  assert property (even == ~counter[0]);
  ap_parity_xor:assert property (even ^ odd);

  // XOR function correctness
  ap_xor_fn:    assert property (xor_out == (a ^ b));

  // out_comb correctness (accounts for width truncation of "counter")
  ap_out_even:  assert property (even |-> out_comb == xor_out);
  ap_out_odd:   assert property (odd  |-> out_comb == 1'b1);

  // No X on key state/outputs at sampling edge
  ap_no_x:      assert property (!$isunknown({counter, even, odd, xor_out, out_comb}));

  // Coverage
  cv_reset:     cover property (@(posedge reset) 1);
  cv_wrap:      cover property (disable iff (reset) (counter==4'hF ##1 counter==4'h0));
  cv_even0:     cover property (disable iff (reset) (even && xor_out==1'b0 && out_comb==1'b0));
  cv_even1:     cover property (disable iff (reset) (even && xor_out==1'b1 && out_comb==1'b1));
  cv_odd_seen:  cover property (disable iff (reset) (odd && out_comb==1'b1));
  cv_xor_tgl:   cover property (xor_out ##1 !xor_out);

endmodule

bind top_module top_module_sva sva_i (.*);