// SVA for counter_3bit
// Focused, high-quality checks and concise coverage

module counter_3bit_sva (
  input logic        clk,
  input logic        rst,
  input logic        en,
  input logic [2:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on key signals
  assert property (!$isunknown({rst, en, count}));

  // Synchronous reset: next cycle after rst high, count is 0
  assert property (rst |-> ##1 (count == 3'd0));

  // Hold when !en (outside reset)
  assert property (disable iff (rst)
    !en |-> ##1 (count == $past(count))
  );

  // Increment by 1 modulo 8 when en (outside reset)
  assert property (disable iff (rst)
    en |-> ##1 (count == (($past(count)==3'd7) ? 3'd0 : $past(count)+3'd1))
  );

  // Coverage: reset effect visible
  cover property (rst ##1 (count == 3'd0));

  // Coverage: wrap-around when en is high
  cover property (disable iff (rst)
    (en && count==3'd7) ##1 (en && count==3'd0)
  );

  // Coverage: full cycle through 0..7 with en held high
  cover property (disable iff (rst)
    (count==3'd0 && en)
    ##1 (count==3'd1 && en)
    ##1 (count==3'd2 && en)
    ##1 (count==3'd3 && en)
    ##1 (count==3'd4 && en)
    ##1 (count==3'd5 && en)
    ##1 (count==3'd6 && en)
    ##1 (count==3'd7 && en)
    ##1 (count==3'd0)
  );
endmodule

bind counter_3bit counter_3bit_sva u_counter_3bit_sva (
  .clk(clk), .rst(rst), .en(en), .count(count)
);