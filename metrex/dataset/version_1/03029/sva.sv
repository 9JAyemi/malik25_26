// SVA for up_counter_4bit
// Bind example: bind up_counter_4bit up_counter_4bit_sva sva(.clk(clk), .rst(rst), .en(en), .count(count));

module up_counter_4bit_sva (
  input  logic        clk,
  input  logic        rst,   // active-low async reset
  input  logic        en,
  input  logic [3:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity (no X/Z on key signals at clock edges)
  assert property ( !$isunknown(rst) );
  assert property ( !$isunknown(en) );
  assert property ( !$isunknown(count) );

  // Asynchronous reset forces count to 0 immediately and holds it at 0 while rst==0
  assert property ( @(negedge rst) count == 4'h0 );
  assert property ( (!rst) |=> (count == 4'h0) );

  // One-step functional relation out of reset:
  // count advances by +1 when en=1, otherwise holds (mod-16)
  assert property (
    rst && $past(rst)
    |=> count == (($past(count) + ($past(en) ? 4'd1 : 4'd0)) [3:0])
  );

  // Optional explicit rollover check (redundant with the relation but clearer on failure)
  assert property (
    rst && $past(rst) && $past(en) && $past(count)==4'hF
    |=> count==4'h0
  );

  // Coverage

  // See async reset assertion and deassertion
  cover property ( @(negedge rst) 1'b1 );
  cover property ( @(posedge clk) $rose(rst) );

  // See an enabled increment and a hold
  cover property ( rst && $past(rst) && $past(en)
                   && count == (($past(count)+4'd1)[3:0]) );
  cover property ( rst && $past(rst) && !$past(en)
                   && count == $past(count) );

  // See rollover from F -> 0 with en=1
  cover property ( rst && $past(rst) && $past(en) && $past(count)==4'hF
                   && count==4'h0 );

  // See a full 16-step wrap starting from 0 with continuous enable
  cover property ( rst && count==4'h0 ##1 (rst && en)[*16] ##1 (rst && count==4'h0) );

  // See deasserted reset followed by immediate first increment when en=1
  cover property ( $rose(rst) ##1 (en && count==4'd1) );

endmodule