// SVA for jserialaddlab
// Bind this file to the DUT: bind jserialaddlab jserialaddlab_sva;

module jserialaddlab_sva;

  // Access DUT scope via bind (signals: clk, reset, a, b, sum, carry, cout, so, count, cin, cut)
  default clocking cb @(posedge clk); endclocking

  // Reset behavior (synchronous clears)
  ap_reset_clear: assert property (reset |-> (cin==0 && cout==0 && so==4'b0 && count==3'b0));

  // No X/Z after reset deassertion
  ap_no_x: assert property (disable iff (reset) !$isunknown({a,b,cin,cut,sum,carry,cout,so,count}));

  // Combinational definitions sampled on clock
  ap_sum_def:   assert property (sum == (a ^ b ^ cin));
  ap_cut_def:   assert property (cut == ((a & b) | (a & cin) | (b & cin)));
  ap_carry_def: assert property (carry == ((count==3'b100) ? 1'b0 : cut));
  ap_carry_zero_at4: assert property (count==3'b100 |-> carry==1'b0);

  // Sequential updates (mask boundary across reset)
  ap_cin_q:   assert property (!reset && !$past(reset,1,1) |-> cin  == $past(carry));
  ap_cout_q:  assert property (!reset && !$past(reset,1,1) |-> cout == (($past(count)==3'b100) ? (($past(a) & 4'b1000)[0]) : 1'b0));
  ap_so_q:    assert property (!reset && !$past(reset,1,1) |-> so   == { $past(sum), $past(so[3:1]) });
  ap_count_q: assert property (!reset && !$past(reset,1,1) |-> count== ($past(cut) ? $past(count)+3'b001 : 3'b000));

  // Coverage
  cp_reach4:         cover property (!reset && count==3'b100);
  cp_cin_from_carry: cover property (!reset && !$past(reset,1,1) && $past(carry) && cin);
  cp_so_shifted:     cover property (!reset && !$past(reset,1,1) && $past(so)!=so && so!=4'b0);
  cp_cout_phase:     cover property (!reset && !$past(reset,1,1) && ($past(count)==3'b100));

endmodule

bind jserialaddlab jserialaddlab_sva;