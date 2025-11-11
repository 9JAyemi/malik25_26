// SVA checker for up_counter
module up_counter_sva (
  input logic       clk,
  input logic       reset,
  input logic [3:0] count_out,
  input logic       j,
  input logic       k
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (reset |-> (count_out==4'b0000 && j==1'b0 && k==1'b0));

  // No X/Z on key signals when active
  assert property (!reset |-> !$isunknown({count_out,j,k}));

  // Count update rules (mod-16)
  assert property (disable iff (reset) ({j,k}==2'b00 |=> count_out == $past(count_out)+1));
  assert property (disable iff (reset) ({j,k}!=2'b00 |=> count_out == $past(count_out)));

  // Any count change must be +1
  assert property (disable iff (reset) (count_out != $past(count_out) |-> count_out == $past(count_out)+1));

  // j,k next-state mapping
  assert property (disable iff (reset) ({j,k}==2'b00 |=> {j,k}==2'b10));
  assert property (disable iff (reset) ({j,k}==2'b01 |=> {j,k}==2'b01));
  assert property (disable iff (reset) ({j,k}==2'b10 |=> {j,k}==2'b10));
  assert property (disable iff (reset) ({j,k}==2'b11 |=> {j,k}==2'b11));

  // First cycle after reset deassertion
  assert property ($fell(reset) |=> (count_out == $past(count_out)+1) && ({j,k}==2'b10));

  // Coverage
  cover property ($rose(reset));
  cover property (disable iff (reset) ({j,k}==2'b00 ##1 ({j,k}==2'b10 && count_out == $past(count_out)+1)));
endmodule

// Bind into DUT (accesses internal j,k)
bind up_counter up_counter_sva u_up_counter_sva (
  .clk(clk),
  .reset(reset),
  .count_out(count_out),
  .j(j),
  .k(k)
)