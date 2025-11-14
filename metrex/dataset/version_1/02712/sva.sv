// SVA checker for bcd_ctr
module bcd_ctr_sva
(
  input logic        clk,
  input logic        ar,    // active-low async reset
  input logic        en,
  input logic [3:0]  dig1, dig2, dig3,
  input logic        dig1_carry, dig2_carry, dig3_carry
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!ar);

  // Basic well-formedness
  a_ranges:        assert property ( (dig1 inside {[4'd0:4'd9]}) && (dig2 inside {[4'd0:4'd9]}) && (dig3 inside {[4'd0:4'd9]}) );
  a_no_x:          assert property ( !$isunknown({ar,en,dig1,dig2,dig3}) );

  // Carry definition consistency
  a_c1_def:        assert property ( dig1_carry == (dig1 == 4'd9) );
  a_c2_def:        assert property ( dig2_carry == (dig1_carry && (dig2 == 4'd9)) );
  a_c3_def:        assert property ( dig3_carry == (dig2_carry && (dig3 == 4'd9)) );

  // While reset is asserted low, outputs must be 0 on every clock
  a_reset_holds_0: assert property ( !ar |-> (dig1==4'd0 && dig2==4'd0 && dig3==4'd0) );

  // Hold when stalled (either en==0 or saturated at 999)
  a_hold_stall:    assert property ( (en==1'b0 || dig3_carry) |=> $stable({dig3,dig2,dig1}) );

  // Increment behavior (enabled and not saturated)
  // Case 1: no carry from dig1
  a_inc_no_carry:  assert property (
                      en && !dig3_carry && !dig1_carry
                      |=> (dig1 == $past(dig1)+4'd1) && (dig2 == $past(dig2)) && (dig3 == $past(dig3))
                    );

  // Case 2: carry from dig1 only (dig2 != 9)
  a_inc_carry1:    assert property (
                      en && !dig3_carry &&  dig1_carry && !dig2_carry
                      |=> (dig1 == 4'd0) && (dig2 == $past(dig2)+4'd1) && (dig3 == $past(dig3))
                    );

  // Case 3: carry from dig2 as well (dig1==9, dig2==9, dig3!=9)
  a_inc_carry2:    assert property (
                      en && !dig3_carry &&  dig2_carry
                      |=> (dig1 == 4'd0) && (dig2 == 4'd0) && (dig3 == $past(dig3)+4'd1)
                    );

  // Coverage
  c_simple_inc:    cover property ( en && !dig3_carry && !dig1_carry ##1 (dig1 == $past(dig1)+4'd1) );
  c_carry1:        cover property ( en && !dig3_carry &&  dig1_carry && !dig2_carry ##1 (dig1==0 && dig2==$past(dig2)+1) );
  c_carry2:        cover property ( en &&  dig2_carry && !dig3_carry ##1 (dig1==0 && dig2==0 && dig3==$past(dig3)+1) );
  c_saturate_hold: cover property ( (dig3==9 && dig2==9 && dig1==9) && en ##1 $stable({dig3,dig2,dig1}) );
  c_reset:         cover property ( !ar ##1 ar ##1 (dig1==0 && dig2==0 && dig3==0) );

endmodule

// Bind into DUT (connects internal carries by name)
bind bcd_ctr bcd_ctr_sva sva_i (.*);