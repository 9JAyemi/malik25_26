// SVA for top_module
// Bind-in module (no DUT changes needed)
module top_module_sva;
  // Inherit DUT scope signals via bind (no ports)
  // clk, A, B, shift, control, parallel_load, shift_reg, decoder_out, Y

  // clock/past_valid
  bit past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid || $isunknown({A,B,shift,control,parallel_load,shift_reg}));

  // Parallel load has priority over shift/rotate
  assert property (shift |=> shift_reg == $past(parallel_load));

  // Rotate-right when control==0 and no load
  assert property ((!shift && !control) |=> shift_reg == { $past(shift_reg[0]), $past(shift_reg[2:1]) });

  // "Left" operation as coded (truncated concat): {sr[1:0], sr[1]}
  assert property ((!shift && control) |=> shift_reg == { $past(shift_reg[1:0]), $past(shift_reg[1]) });

  // Decoder: exactly one bit set, confined to lower 8 bits
  assert property (1 |-> ##1 $onehot(decoder_out) && decoder_out[15:8] == 8'h00);

  // Exact decoder value from prior shift_reg and current A,B
  assert property (1 |-> ##1 decoder_out == (16'h1 << (
           ({$past(A),$past(B)}==2'b00) ? $past(shift_reg) :
           ({$past(A),$past(B)}==2'b01) ? ($past(shift_reg) >> 1) :
           ({$past(A),$past(B)}==2'b10) ? ($past(shift_reg) >> 2) :
                                          ($past(shift_reg) >> 3) )));

  // Y lags decoder_out by one cycle and remains one-hot in lower 8 bits
  assert property (1 |-> ##1 Y == $past(decoder_out));
  assert property (1 |-> ##2 $onehot(Y) && Y[15:8] == 8'h00);

  // No X/Z on outputs after update
  assert property (1 |-> ##1 !$isunknown(decoder_out));
  assert property (1 |-> ##1 !$isunknown(Y));

  // Coverage
  cover property (shift |=> shift_reg == $past(parallel_load));
  cover property (!shift && !control);   // rotate-right
  cover property (!shift &&  control);   // coded "left" op
  cover property ({A,B}==2'b00);
  cover property ({A,B}==2'b01);
  cover property ({A,B}==2'b10);
  cover property ({A,B}==2'b11);
endmodule

bind top_module top_module_sva sva_i;