// SVA for a25_multiply
// Bind into DUT: bind a25_multiply a25_multiply_sva();

module a25_multiply_sva();
  default clocking cb @ (posedge i_clk); endclocking

  // Basic combinational correctness
  assert property (multiplier      == {2'd0, i_a_in});
  assert property (multiplier_bar  == (~{2'd0, i_a_in}) + 34'd1);
  assert property (sum34_b == (product[1:0]==2'b01 ? multiplier :
                               product[1:0]==2'b10 ? multiplier_bar : 34'd0));
  assert property (sum      == product[67:34] + sum34_b);
  assert property (sum_acc1 == {1'b0, product[32:1]} + {1'b0, i_a_in});

  // Output mapping
  assert property (o_out   == product[32:1]);
  assert property (o_flags == {product[32], product[32:1]==32'd0});

  // Register stability on stall or when not executing
  assert property (i_core_stall |=> $stable({count, product, o_done}));
  assert property (!i_core_stall && !i_execute |=> $stable({count, product, o_done}));

  // Count stays within range
  assert property (count <= 6'd35);

  // Counter next-state behavior when updating
  assert property (!i_core_stall && i_execute && count==6'd0 |=> count == (enable ? 6'd1 : 6'd0));
  assert property (!i_core_stall && i_execute && count>=6'd1 && count<=6'd33 |=> count == $past(count)+6'd1);
  assert property (!i_core_stall && i_execute && count==6'd34 && !accumulate |=> count == 6'd0);
  assert property (!i_core_stall && i_execute && count==6'd35 &&  accumulate |=> count == 6'd0);

  // Product next-state behavior when updating
  // Init load
  assert property (!i_core_stall && i_execute && count==6'd0 |=> (product[0] == 1'b0 && product[32:1] == i_b_in));
  // Iterations 1..33 (Booth step + shift)
  assert property (!i_core_stall && i_execute && count>=6'd1 && count<=6'd33
                   |=> product == {sum[33], sum, $past(product[33:1])});
  // Accumulate step at 34
  assert property (!i_core_stall && i_execute && count==6'd34 && accumulate
                   |=> product == {$past(product[64:33]), sum_acc1[31:0], 1'b0});
  // Hold at terminal steps when no explicit write
  assert property (!i_core_stall && i_execute && count==6'd34 && !accumulate |=> product == $past(product));
  assert property (!i_core_stall && i_execute && count==6'd35 &&  accumulate |=> product == $past(product));

  // o_done pulse behavior under continuous execute
  assert property (!i_core_stall && i_execute && count==6'd31 |=> o_done);
  assert property (!i_core_stall && i_execute && count==6'd31 ##1 (!i_core_stall && i_execute) |-> !o_done);

  // Coverage: exercise key paths
  // - Non-accumulate: reach 34 then return to 0
  cover property (!i_core_stall && i_execute && count==6'd0 && enable && !accumulate
                  ##[1:40] count==6'd34 ##1 count==6'd0);
  // - Accumulate: reach 35 then return to 0
  cover property (!i_core_stall && i_execute && count==6'd0 && enable && accumulate
                  ##[1:45] count==6'd35 ##1 count==6'd0);
  // - sum34_b selection cases
  cover property (product[1:0]==2'b01 && sum34_b==multiplier);
  cover property (product[1:0]==2'b10 && sum34_b==multiplier_bar);
  cover property ((product[1:0]==2'b00 || product[1:0]==2'b11) && sum34_b==34'd0);
  // - o_done assertion
  cover property (!i_core_stall && i_execute && count==6'd31 ##1 o_done);
endmodule