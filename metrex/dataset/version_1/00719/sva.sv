// SVA for booth_multiplier
// Bind into the DUT to access internal signals
bind booth_multiplier booth_multiplier_sva();

module booth_multiplier_sva();
  default clocking cb @(posedge clk); endclocking

  // Reset behavior (synchronous)
  assert property (@cb reset |-> (state==2'b00 && count==5'd0 && P_reg==32'd0 && done==1'b0));

  // Idle hold and start handshake
  assert property (@cb disable iff (reset) (state==2'b00 && !start) |=> state==2'b00);
  assert property (@cb disable iff (reset) (state==2'b00 && start) |=> (state==2'b01 && A_reg==$past(A) && B_reg==$past(B)));

  // Iteration: count increments while <16
  assert property (@cb disable iff (reset) (state==2'b01 && count<5'd16) |=> count==$past(count)+1);

  // Iteration: arithmetic right shift of B_reg
  assert property (@cb disable iff (reset) (state==2'b01 && count<5'd16)
                   |=> (B_reg[15]==$past(B_reg[15]) && B_reg[14:0]==$past(B_reg[15:1])));

  // Iteration: P_reg update rules (add/sub/hold)
  assert property (@cb disable iff (reset)
                   (state==2'b01 && count<5'd16 &&  B_reg[0] && !P_reg[0])
                   |=> P_reg==$past(P_reg)+{{16{$past(A_reg[15])}},$past(A_reg)});
  assert property (@cb disable iff (reset)
                   (state==2'b01 && count<5'd16 && !B_reg[0] &&  P_reg[0])
                   |=> P_reg==$past(P_reg)-{{16{$past(A_reg[15])}},$past(A_reg)});
  assert property (@cb disable iff (reset)
                   (state==2'b01 && count<5'd16 && !(B_reg[0]^P_reg[0]))
                   |=> P_reg==$past(P_reg));

  // Leave iteration when count>=16
  assert property (@cb disable iff (reset) (state==2'b01 && !(count<5'd16)) |=> state==2'b10);

  // Output state: P update and done, then return to idle
  assert property (@cb disable iff (reset) (state==2'b10) |-> (done && P==P_comp));
  assert property (@cb disable iff (reset) (state==2'b10) |=> state==2'b00);

  // P should only change in output state
  assert property (@cb disable iff (reset) (state!=2'b10) |=> P==$past(P));

  // done should only assert in output state (flags sticky-done bugs)
  assert property (@cb disable iff (reset) done |-> state==2'b10);

  // Combinational definitions sanity
  assert property (@cb disable iff (reset) B_comp == (~B + 16'd1));

  // End-to-end functional correctness (signed 16x16 -> 32)
  property p_signed_mult_correct;
    logic signed [15:0] a0, b0;
    (state==2'b00 && start, a0=A, b0=B)
      |-> ##[1:$] (state==2'b10 && done && $signed(P)==$signed(a0)*$signed(b0));
  endproperty
  assert property (@cb disable iff (reset) p_signed_mult_correct);

  // Coverage: start-to-done, 16-cycle run from count==0, and sign combinations
  cover property (@cb disable iff (reset) (state==2'b00 && start) ##[1:$] (state==2'b10 && done));
  cover property (@cb disable iff (reset) (state==2'b00 && start && count==5'd0)
                  ##1 (state==2'b01 && count<5'd16)[*16] ##1 state==2'b10 && done);
  cover property (@cb disable iff (reset) (state==2'b00 && start && A==16'sd0) ##[1:$] (state==2'b10 && done && P==32'sd0));
  cover property (@cb disable iff (reset) (state==2'b00 && start &&  A[15]==0 &&  B[15]==0) ##[1:$] (state==2'b10 && done));
  cover property (@cb disable iff (reset) (state==2'b00 && start &&  A[15]==1 &&  B[15]==0) ##[1:$] (state==2'b10 && done));
  cover property (@cb disable iff (reset) (state==2'b00 && start &&  A[15]==0 &&  B[15]==1) ##[1:$] (state==2'b10 && done));
  cover property (@cb disable iff (reset) (state==2'b00 && start &&  A[15]==1 &&  B[15]==1) ##[1:$] (state==2'b10 && done));
endmodule