// SVA for the provided design. Concise, high-signal-coverage, focused on key behavior.

// ---------------- counter checks ----------------
module counter_sva (input logic clk,
                    input logic reset,
                    input logic direction,
                    input logic [2:0] count);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  assert property (cb !$isunknown({reset, direction}));
  assert property (cb !reset |-> !$isunknown(count));

  // Reset behavior
  assert property (cb reset |=> count == 3'b000);
  assert property (cb reset && $past(reset) |-> count == 3'b000);

  // Count up/down (mod-8), only when previous cycle not in reset
  assert property (cb (!reset && $past(!reset) && $past(direction))
                   |-> count == ($past(count) + 3'd1));
  assert property (cb (!reset && $past(!reset) && !$past(direction))
                   |-> count == ($past(count) - 3'd1));

  // Coverage: reset pulse, both directions, wrap up/down
  cover property (cb $rose(reset));
  cover property (cb !reset && $past(!reset) && $past(direction)
                      && count == $past(count) + 3'd1);
  cover property (cb !reset && $past(!reset) && !$past(direction)
                      && count == $past(count) - 3'd1);
  cover property (cb !reset && $past(!reset) && $past(direction)
                      && $past(count)==3'b111 && count==3'b000); // up wrap
  cover property (cb !reset && $past(!reset) && !$past(direction)
                      && $past(count)==3'b000 && count==3'b111); // down wrap
endmodule

// ---------------- comparator checks ----------------
module comparator_sva (input logic [3:0] a,
                       input logic [3:0] b,
                       input logic       equal);
  // Combinational equivalence
  assert property (equal == (a == b));

  // Coverage: both compare outcomes
  cover property (a == b);
  cover property (a != b);
endmodule

// ---------------- final_output checks ----------------
module final_output_sva (input logic [2:0] count,
                         input logic       equal,
                         input logic [2:0] out_final);
  // Combinational pass/zero mux
  assert property (out_final == (equal ? count : 3'b000));

  // Coverage: both mux paths
  cover property (equal && out_final == count);
  cover property (!equal && out_final == 3'b000);
endmodule

// ---------------- top-level end-to-end check ----------------
module top_sva (input logic        clk,
                input logic [3:0]  a,
                input logic [3:0]  b,
                input logic [2:0]  count,
                input logic [2:0]  out_final);
  default clocking cb @(posedge clk); endclocking

  // End-to-end: out_final must reflect a==b gating of count
  assert property (cb !$isunknown({a,b}) |-> out_final == ((a==b) ? count : 3'b000));

  // Coverage: observe both gated outcomes
  cover property (cb (a==b) && out_final == count);
  cover property (cb (a!=b) && out_final == 3'b000);
endmodule

// ---------------- binds ----------------
bind counter      counter_sva      counter_chk   (.clk(clk), .reset(reset), .direction(direction), .count(count));
bind comparator   comparator_sva   comparator_chk(.a(a), .b(b), .equal(equal));
bind final_output final_output_sva finalout_chk  (.count(count), .equal(equal), .out_final(out_final));
bind top_module   top_sva          top_chk       (.clk(clk), .a(a), .b(b), .count(count), .out_final(out_final));