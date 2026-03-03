module binary_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // Assertions
  a_reset_clears: assert property (reset |=> count == 4'h0);

  a_mod16_next: assert property (
    disable iff (reset)
    1'b1 |=> count == ($past(count) == 4'hF ? 4'h0 : $past(count) + 4'h1)
  );

  a_no_xz: assert property (disable iff (reset or $initstate) !$isunknown(count));

  // Coverage
  c_reset_pulse: cover property ($rose(reset));

  c_wrap: cover property (disable iff (reset) (count == 4'hF) ##1 (count == 4'h0));

  c_exit_reset_to_one: cover property ($fell(reset) ##1 (count == 4'h1));

  c_full_cycle: cover property (
    disable iff (reset)
    (count==4'h0) ##1 (count==4'h1) ##1 (count==4'h2) ##1 (count==4'h3) ##1
    (count==4'h4) ##1 (count==4'h5) ##1 (count==4'h6) ##1 (count==4'h7) ##1
    (count==4'h8) ##1 (count==4'h9) ##1 (count==4'hA) ##1 (count==4'hB) ##1
    (count==4'hC) ##1 (count==4'hD) ##1 (count==4'hE) ##1 (count==4'hF) ##1
    (count==4'h0)
  );
endmodule

bind binary_counter binary_counter_sva u_binary_counter_sva (.*);