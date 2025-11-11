// SVA for priority_bcd_mux
// Bindable, concise, checks key next-state semantics and covers main modes.

module priority_bcd_mux_sva (
  input logic         clk,
  input logic [3:0]   A, B, C, D,
  input logic [1:0]   S,
  input logic [3:0]   binary_in,
  input logic [6:0]   seven_segment_out,
  input logic         EN1, EN2, EN3,
  input logic [3:0]   priority_input,
  input logic [3:0]   bcd_out,
  input logic [1:0]   digit_counter
);

  default clocking cb @(posedge clk); endclocking
  bit past_valid; always_ff @(posedge clk) past_valid <= 1'b1;

  // X-check after first cycle
  assert property (past_valid |-> !$isunknown({seven_segment_out, EN1, EN2, EN3,
                                              digit_counter, bcd_out, priority_input}));

  // Digit counter must increment modulo-4
  assert property (past_valid |-> digit_counter == ($past(digit_counter)==2'd3 ? 2'd0
                                                                                 : $past(digit_counter)+2'd1));

  // EN mapping (based on previous digit_counter due to NBA semantics)
  assert property (past_valid && $past(digit_counter)==2'd0 |->  EN1 && !EN2 && !EN3);
  assert property (past_valid && $past(digit_counter)==2'd1 |-> !EN1 &&  EN2 && !EN3);
  assert property (past_valid && $past(digit_counter)==2'd2 |-> !EN1 && !EN2 &&  EN3);
  assert property (past_valid && $past(digit_counter)==2'd3 |-> !EN1 && !EN2 && !EN3);
  // One-hot-or-zero on enables
  assert property ($onehot0({EN3,EN2,EN1}));

  // Binary->BCD pipeline (bcd_out is function of previous digit_counter/binary_in)
  assert property (past_valid && $past(digit_counter)==2'd0 |-> bcd_out == ($past(binary_in) % 10));
  assert property (past_valid && $past(digit_counter)==2'd1 |-> bcd_out == (($past(binary_in)/10) % 10));
  assert property (past_valid && $past(digit_counter)==2'd2 |-> bcd_out == (($past(binary_in)/100) % 10));
  assert property (past_valid && $past(digit_counter)==2'd3 |-> bcd_out == (($past(binary_in)/1000) % 10));
  // BCD range
  assert property (bcd_out < 10);

  // Priority encoder semantics (as coded)
  assert property (past_valid &&
                   { $past(A), $past(B), $past(C), $past(D) } == 16'h000E |-> priority_input == $past(A));
  assert property (past_valid &&
                   { $past(A), $past(B), $past(C), $past(D) } == 16'h000D |-> priority_input == $past(B));
  assert property (past_valid &&
                   { $past(A), $past(B), $past(C), $past(D) } == 16'h000B |-> priority_input == $past(C));
  assert property (past_valid &&
                   { $past(A), $past(B), $past(C), $past(D) } == 16'h0007 |-> priority_input == $past(D));
  assert property (past_valid &&
                   !({ $past(A), $past(B), $past(C), $past(D) } inside {16'h000E,16'h000D,16'h000B,16'h0007})
                   |-> priority_input == 4'b0000);

  // seven_segment_out selection (depends on previous S, bcd_out, priority_input)
  assert property (past_valid && $past(S)==2'b00 |-> seven_segment_out == {3'b000, $past(bcd_out)});
  assert property (past_valid && $past(S)==2'b01 |-> seven_segment_out == {3'b000, $past(priority_input)});
  assert property (past_valid && $past(S)==2'b10 |-> seven_segment_out == 7'b111_1111);
  assert property (past_valid && $past(S)==2'b11 |-> seven_segment_out == 7'b000_0000);

  // Coverage
  cover property (past_valid && digit_counter==0 ##1 digit_counter==1 ##1 digit_counter==2 ##1 digit_counter==3 ##1 digit_counter==0);
  cover property ($past(S)==2'b10 && seven_segment_out==7'b111_1111);
  cover property ($past(S)==2'b11 && seven_segment_out==7'b000_0000);
  cover property ($past(S)==2'b00 && seven_segment_out[6:4]==3'b000);
  cover property (EN1); cover property (EN2); cover property (EN3);
  cover property (bcd_out==0); cover property (bcd_out==9);
  cover property ({A,B,C,D} == 16'h000E);
  cover property ({A,B,C,D} == 16'h000D);
  cover property ({A,B,C,D} == 16'h000B);
  cover property ({A,B,C,D} == 16'h0007);

endmodule

// Bind into DUT
bind priority_bcd_mux priority_bcd_mux_sva sva (
  .clk               (clk),
  .A                 (A),
  .B                 (B),
  .C                 (C),
  .D                 (D),
  .S                 (S),
  .binary_in         (binary_in),
  .seven_segment_out (seven_segment_out),
  .EN1               (EN1),
  .EN2               (EN2),
  .EN3               (EN3),
  .priority_input    (priority_input),
  .bcd_out           (bcd_out),
  .digit_counter     (digit_counter)
);