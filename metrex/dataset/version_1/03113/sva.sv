// SVA for signed_gte_4bit
module signed_gte_4bit_sva;
  default clocking cb @(posedge clk); endclocking

  // Stage legality and toggling
  a_stage_legal:       assert property ( !$isunknown(stage) |-> stage inside {2'b00,2'b01} );
  a_stage_00_to_01:    assert property ( disable iff($isunknown(stage)) stage==2'b00 |=> stage==2'b01 );
  a_stage_01_to_00:    assert property ( disable iff($isunknown(stage)) stage==2'b01 |=> stage==2'b00 );

  // Register capture/hold behavior
  a_cap_regs:          assert property ( stage==2'b00 |=> (A_reg==$past(A) && B_reg==$past(B)) );
  a_hold_regs:         assert property ( stage==2'b01 |->  ($stable(A_reg) && $stable(B_reg)) );
  a_regs_change_only_on_cap:
                       assert property ( $changed(A_reg) |-> $past(stage)==2'b00 );
  b_regs_change_only_on_cap:
                       assert property ( $changed(B_reg) |-> $past(stage)==2'b00 );

  // Output behavior and correctness
  a_gte_stable_in_cap: assert property ( stage==2'b00 |-> $stable(GTE) );
  a_gte_changes_only_on_eval:
                       assert property ( $changed(GTE) |-> ($past(stage)==2'b00 && stage==2'b01) );

  a_gte_correct:       assert property (
                         (stage==2'b01 && $past(stage)==2'b00)
                         |-> GTE == ($signed($past(A)) >= $signed($past(B)))
                       );
  a_gte_known_when_valid:
                       assert property ( (stage==2'b01 && $past(stage)==2'b00) |-> !$isunknown(GTE) );

  // Functional coverage
  c_stage_cycle:       cover property ( stage==2'b00 ##1 stage==2'b01 ##1 stage==2'b00 );

  c_result_true:       cover property ( (stage==2'b01 && $past(stage)==2'b00) && GTE==1 );
  c_result_false:      cover property ( (stage==2'b01 && $past(stage)==2'b00) && GTE==0 );
  c_equal_case:        cover property ( (stage==2'b01 && $past(stage)==2'b00)
                                        && ($signed($past(A))==$signed($past(B))) && GTE==1 );

  // Signedness stress points (-8 vs +7, +7 vs -8)
  c_signed_min_lt_max: cover property ( (stage==2'b01 && $past(stage)==2'b00)
                                        && ($past(A)==4'sh8) && ($past(B)==4'sh7) && GTE==0 );
  c_signed_max_gt_min: cover property ( (stage==2'b01 && $past(stage)==2'b00)
                                        && ($past(A)==4'sh7) && ($past(B)==4'sh8) && GTE==1 );
endmodule

bind signed_gte_4bit signed_gte_4bit_sva sva();