// Assertions for rrab: bindable SVA module + bind
module rrab_sva (
  input clk, input reset_n,
  input [1:0] request, input [1:0] grant,
  input [1:0] grant_i, input last_winner, input winner
);
  default clocking cb @(posedge clk); endclocking
  // reset checks (not disabled during reset)
  assert property (@(posedge clk) !reset_n |-> (grant==2'b00 && last_winner==1'b0));

  // disable assertions below during reset
  default disable iff (!reset_n);

  // basic safety
  assert property (($onehot0(grant)));
  assert property (((grant & ~request) == 2'b00));
  assert property (request==2'b00 |-> grant==2'b00);
  assert property (request==2'b01 |-> grant==2'b01);
  assert property (request==2'b10 |-> grant==2'b10);
  assert property (request==2'b11 |-> (grant inside {2'b01,2'b10}));
  assert property (!$isunknown({grant,last_winner}));

  // next-state winner update rules
  assert property (request==2'b00 |=> last_winner == $past(last_winner));
  assert property (request==2'b01 |=> last_winner == 1'b0);
  assert property (request==2'b10 |=> last_winner == 1'b1);
  assert property (request==2'b11 |=> last_winner == ~ $past(last_winner));

  // persistent both-requests -> alternating grants
  assert property (request==2'b11 |=> (request==2'b11 && grant != $past(grant)));

  // internal comb correctness
  assert property (winner == ((grant_i==2'b00) ? last_winner : grant_i[1]));

  // coverage
  cover property (request==2'b00 && grant==2'b00);
  cover property (request==2'b01 && grant==2'b01);
  cover property (request==2'b10 && grant==2'b10);
  cover property (request==2'b11 && (grant inside {2'b01,2'b10}));
  cover property (request==2'b11 |=> (request==2'b11 && grant != $past(grant)));
  cover property (request==2'b00 |=> last_winner == $past(last_winner));
  cover property (request==2'b01 |=> last_winner == 1'b0);
  cover property (request==2'b10 |=> last_winner == 1'b1);
endmodule

bind rrab rrab_sva u_rrab_sva(
  .clk(clk),
  .reset_n(reset_n),
  .request(request),
  .grant(grant),
  .grant_i(grant_i),
  .last_winner(last_winner),
  .winner(winner)
);