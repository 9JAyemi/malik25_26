// SVA for fsm_longest_sequence_detection
// Bind-in module that references DUT internals directly
module fsm_longest_sequence_detection_sva;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Legal state encoding after reset deasserts
  assert property (state inside {S0,S1,S2,S3,S4});

  // Strong reset behavior check (override default disable)
  assert property (disable iff (1'b0) @(posedge clk)
                   reset |=> (state==S0 && longest_sequence==3'b000));

  // S0 transitions
  assert property (state==S0 && data[7]==1 |=> state==S1);
  assert property (state==S0 && data[7]==0 |=> state==S0);

  // S1 transitions and output update
  assert property (state==S1 && data==8'hFF |=> state==S4 && longest_sequence==3'b111);
  assert property (state==S1 && data!=8'hFF && data[7]==1 |=> state==S2);
  assert property (state==S1 && data[7]==0 |=> state==S0);

  // S2 transitions and output update
  assert property (state==S2 && data==8'hFF |=> state==S4 && longest_sequence==3'b111);
  assert property (state==S2 && data!=8'hFF && data[7:6]==2'b11 |=> state==S3);
  assert property (state==S2 && data[7]==0 |=> state==S0);
  assert property (state==S2 && data!=8'hFF && data[7:6]!=2'b11 && data[7]==1 |=> state==S2);

  // S3 transitions and output update
  assert property (state==S3 && data==8'hFF |=> state==S4 && longest_sequence==3'b111);
  assert property (state==S3 && data!=8'hFF && data[7]==1 |=> state==S3);
  assert property (state==S3 && data[7]==0 |=> state==S0);

  // S4 transitions
  assert property (state==S4 && data==8'hFF |=> state==S4);
  assert property (state==S4 && data!=8'hFF |=> state==S0);

  // longest_sequence behavior
  // Only updates on 8'hFF in S1/S2/S3; otherwise holds value
  assert property (!(state inside {S1,S2,S3} && data==8'hFF) |=> $stable(longest_sequence));
  // If it changes (outside reset), it must become 3'b111
  assert property ($changed(longest_sequence) |-> longest_sequence==3'b111);

  // No X/Z on key regs after reset deasserts
  assert property (!$isunknown({state,longest_sequence}));

  // Coverage
  cover property (reset ##1 !reset ##1 state==S0);
  cover property (state==S0 && data[7]==1 ##1 state==S1);
  cover property (state==S1 && data!=8'hFF && data[7]==1 ##1 state==S2);
  cover property (state==S2 && data!=8'hFF && data[7:6]==2'b11 ##1 state==S3);
  cover property (state==S2 && data!=8'hFF && data[7:6]==2'b10 ##1 state==S2);
  cover property (state==S3 && data!=8'hFF && data[7]==1 ##1 state==S3);
  cover property (state==S1 && data==8'hFF ##1 state==S4 && longest_sequence==3'b111);
  cover property (state==S2 && data==8'hFF ##1 state==S4 && longest_sequence==3'b111);
  cover property (state==S3 && data==8'hFF ##1 state==S4 && longest_sequence==3'b111);
  cover property (state==S4 && data==8'hFF ##1 state==S4);
  cover property (state==S4 && data!=8'hFF ##1 state==S0);
  cover property (state==S0 && data==8'h00 ##1 state==S0);

endmodule

bind fsm_longest_sequence_detection fsm_longest_sequence_detection_sva sva();