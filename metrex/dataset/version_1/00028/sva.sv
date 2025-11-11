// SVA for lcd_driver: concise, complete functional checking + essential coverage
module lcd_driver_sva (
  input  logic [3:0] data,
  input  logic [1:0] ctrl,
  input  logic [6:0] seg
);

  // Functional equivalence (guarded against X/Z on inputs)
  assert property (@(*)
    (!$isunknown({data,ctrl})) |-> ##0
      seg[3:0] == ((data & {4{ctrl[0]}}) | (~data & {4{ctrl[1]}}))
  );

  assert property (@(*)
    (!$isunknown(ctrl)) |-> ##0 seg[4] == ctrl[0]
  );

  assert property (@(*)
    (!$isunknown(ctrl)) |-> ##0 seg[5] == ctrl[1]
  );

  // Constant output bit
  assert property (@(*)
    seg[6] == 1'b0
  );

  // No-X on outputs when inputs are known
  assert property (@(*)
    (!$isunknown({data,ctrl})) |-> ##0 !$isunknown(seg)
  );

  // Mode-specific behavior (redundant with above, but aids debug and coverage)
  assert property (@(*)
    (!$isunknown({data,ctrl})) && ctrl==2'b00 |-> ##0 seg == 7'b0000000
  );
  assert property (@(*)
    (!$isunknown({data,ctrl})) && ctrl==2'b11 |-> ##0 seg == 7'b0111111
  );
  assert property (@(*)
    (!$isunknown({data,ctrl})) && ctrl==2'b01 |-> ##0
      (seg[3:0]==data && seg[5:4]==2'b01 && seg[6]==1'b0)
  );
  assert property (@(*)
    (!$isunknown({data,ctrl})) && ctrl==2'b10 |-> ##0
      (seg[3:0]==~data && seg[5:4]==2'b10 && seg[6]==1'b0)
  );

  // Coverage: exercise all control modes and representative data mapping
  cover property (@(*) ctrl==2'b00 && seg==7'b0000000);
  cover property (@(*) ctrl==2'b11 && seg==7'b0111111);
  cover property (@(*) ctrl==2'b01 && seg[3:0]==data && seg[5:4]==2'b01 && seg[6]==1'b0);
  cover property (@(*) ctrl==2'b10 && seg[3:0]==~data && seg[5:4]==2'b10 && seg[6]==1'b0);

endmodule

bind lcd_driver lcd_driver_sva sva_i (.*);