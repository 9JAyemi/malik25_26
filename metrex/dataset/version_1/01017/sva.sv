// SVA for counter_with_adder_subtractor
// Focused, high-quality checks and concise coverage

module counter_with_adder_subtractor_sva
(
  input  logic        clk,
  input  logic        RST,       // async active-low
  input  logic        sub,
  input  logic [3:0]  A,
  input  logic [3:0]  B,
  input  logic [3:0]  Q,
  input  logic [3:0]  sum,
  input  logic        overflow,
  input  logic [3:0]  final_output
);

  // Basic sanity: outputs known
  assert property (@(posedge clk) !$isunknown({Q, sum, overflow, final_output}))
    else $error("X/Z detected on outputs");

  // Asynchronous reset effect on posedge clk: Q must be 0 while RST=0
  assert property (@(posedge clk) !RST |-> (Q == 4'd0))
    else $error("Q not 0 during reset");

  // Counter increments by 1 modulo 16 when out of reset
  assert property (@(posedge clk) disable iff (!RST)
                   $past(RST) |-> (Q == ($past(Q)+4'd1)[3:0]))
    else $error("Counter did not increment by 1 mod-16");

  // Adder/subtractor functional result (mod-16)
  assert property (@(posedge clk)
                   sum == (sub ? (A - B) : (A + B))[3:0])
    else $error("sum mismatch with adder/subtractor selection");

  // Overflow semantics (unsigned): add overflow = carry out; sub overflow = borrow (A<B)
  assert property (@(posedge clk)
                   !sub |-> (overflow == (({1'b0,A}+{1'b0,B})[4])))
    else $error("Addition overflow incorrect (expected carry-out)");
  assert property (@(posedge clk)
                   sub |-> (overflow == (A < B)))
    else $error("Subtraction overflow/borrow incorrect (expected A<B)");

  // Final output equals counter + sum (mod-16)
  assert property (@(posedge clk)
                   final_output == (Q + sum)[3:0])
    else $error("final_output != (Q + sum) mod-16");

  // During reset, counter is 0, so final_output must equal sum
  assert property (@(posedge clk) !RST |-> (final_output == sum))
    else $error("final_output != sum while in reset");

  // --------------------------------
  // Concise functional coverage
  // --------------------------------
  // Counter wrap-around
  cover property (@(posedge clk) disable iff (!RST)
                  (Q == 4'hF) ##1 (Q == 4'h0));

  // Exercise both operations and both overflow states
  cover property (@(posedge clk) !sub && overflow);
  cover property (@(posedge clk) !sub && !overflow);
  cover property (@(posedge clk)  sub && overflow);
  cover property (@(posedge clk)  sub && !overflow);

  // final_output wrap (counter+sum exceeds 15)
  cover property (@(posedge clk) ((Q + sum) > 4'hF));

endmodule

// Bind into DUT
bind counter_with_adder_subtractor
  counter_with_adder_subtractor_sva sva_i (
    .clk(clk),
    .RST(RST),
    .sub(sub),
    .A(A),
    .B(B),
    .Q(Q),
    .sum(sum),
    .overflow(overflow),
    .final_output(final_output)
  );