// SVA checker for priority_encoder; bind to both modules

module priority_encoder_sva (input [3:0] in, input [1:0] pos);

  // Output shall never be X/Z
  assert property (@(in or pos) !$isunknown(pos));

  // One-hot mappings
  assert property (@(in) (in==4'b0001) |-> (pos==2'b00));
  assert property (@(in) (in==4'b0010) |-> (pos==2'b01));
  assert property (@(in) (in==4'b0100) |-> (pos==2'b10));
  assert property (@(in) (in==4'b1000) |-> (pos==2'b11));

  // Default behavior: zero or multi-hot -> 00
  assert property (@(in) (!$onehot(in)) |-> (pos==2'b00));

  // No spurious encodings
  assert property (@(in or pos) (pos==2'b01) |-> (in==4'b0010));
  assert property (@(in or pos) (pos==2'b10) |-> (in==4'b0100));
  assert property (@(in or pos) (pos==2'b11) |-> (in==4'b1000));

  // Coverage: all one-hot cases + zero + a multi-hot
  cover property (@(in) in==4'b0001 && pos==2'b00);
  cover property (@(in) in==4'b0010 && pos==2'b01);
  cover property (@(in) in==4'b0100 && pos==2'b10);
  cover property (@(in) in==4'b1000 && pos==2'b11);
  cover property (@(in) in==4'b0000 && pos==2'b00);
  cover property (@(in) ($countones(in)>=2) && pos==2'b00);

endmodule

bind priority_encoder priority_encoder_sva(.in(in), .pos(pos));
bind top_module       priority_encoder_sva(.in(in), .pos(pos));