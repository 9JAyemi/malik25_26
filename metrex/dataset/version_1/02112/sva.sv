// SVA bind file for the design

// Counter assertions
module counter_sva (input CLK, input CLR, input LD, input [3:0] DATA, input [3:0] Q);
  default clocking cb @(posedge CLK); endclocking

  // Async reset immediate effect
  assert property (@(negedge CLR) Q == 4'h0);

  // While in reset, Q holds 0
  assert property (cb !CLR |-> (Q == 4'h0));

  // No X on Q when not in reset
  assert property (cb CLR |-> !$isunknown(Q));

  // Load on LD
  assert property (cb (CLR && LD) |-> (Q == DATA));

  // Increment by 1 (mod 16) when not loading
  assert property (cb (CLR && !LD) |-> (Q == $past(Q) + 4'd1));

  // Explicit wrap check 0xF -> 0x0 when incrementing
  assert property (cb (CLR && !LD && $past(Q) == 4'hF) |-> (Q == 4'h0));

  // Coverage
  cover property (cb $fell(CLR));                               // saw reset assert
  cover property (cb CLR && LD);                                 // saw a load
  cover property (cb (CLR && !LD && $past(Q)==4'hE) ##1
                       (CLR && !LD && Q==4'hF) ##1
                       (CLR && !LD && Q==4'h0));                 // wrap sequence
endmodule

bind counter counter_sva c_sva (.*);


// Bitwise AND assertions (combinational)
module bitwise_and_sva (input [3:0] A, input [3:0] B, input [3:0] Y);
  // Functional equivalence on any relevant change (delta-cycle accurate)
  assert property (@(A or B or Y) 1'b1 |-> ##0 (Y == (A & B)));

  // If inputs known, output must be known
  assert property (@(A or B) !$isunknown({A,B}) |-> ##0 !$isunknown(Y));

  // Coverage: zero, full, mixed
  cover property (@(A or B) ##0 (Y == 4'h0));
  cover property (@(A or B) ##0 (Y == 4'hF));
  cover property (@(A or B) ##0 (Y != 4'h0 && Y != 4'hF));
endmodule

bind bitwise_and bitwise_and_sva ba_sva (.*);


// Functional module assertions (combinational)
module functional_module_sva (input [3:0] counter_output,
                              input [3:0] bitwise_and_output,
                              input [3:0] final_output);
  // Functional equivalence on any relevant change
  assert property (@(counter_output or bitwise_and_output or final_output)
                   1'b1 |-> ##0 (final_output == (bitwise_and_output & counter_output)));

  // If inputs known, output must be known
  assert property (@(counter_output or bitwise_and_output)
                   !$isunknown({counter_output,bitwise_and_output})
                   |-> ##0 !$isunknown(final_output));

  // Coverage: zero, full, mixed
  cover property (@(counter_output or bitwise_and_output) ##0 (final_output == 4'h0));
  cover property (@(counter_output or bitwise_and_output) ##0 (final_output == 4'hF));
  cover property (@(counter_output or bitwise_and_output) ##0 (final_output != 4'h0 && final_output != 4'hF));
endmodule

bind functional_module functional_module_sva fm_sva (.*);


// Top-level end-to-end assertions
module top_module_sva (input CLK, input CLR, input [3:0] DATA, input [3:0] Y,
                       input [3:0] counter_output, input [3:0] bitwise_and_output);
  // End-to-end equivalence: Y must equal counter_output & DATA at all times
  assert property (@(counter_output or DATA or Y)
                   1'b1 |-> ##0 (Y == (counter_output & DATA)));

  // bitwise_and_output should equal counter_output & DATA at all times
  assert property (@(counter_output or DATA or bitwise_and_output)
                   1'b1 |-> ##0 (bitwise_and_output == (counter_output & DATA)));

  // If inputs to path are known, Y must be known
  assert property (@(counter_output or DATA)
                   !$isunknown({counter_output,DATA}) |-> ##0 !$isunknown(Y));

  // Coverage: observe Y zero, full, and wrap-through case reaching 0 after 0xF
  cover property (@(posedge CLK) (CLR && (Y == 4'h0)));
  cover property (@(posedge CLK) (CLR && (Y == 4'hF)));
  cover property (@(posedge CLK)
                  (CLR && (counter_output == 4'hE)) ##1
                  (CLR && (counter_output == 4'hF)) ##1
                  (CLR && (counter_output == 4'h0)));
endmodule

bind top_module top_module_sva t_sva (.*);