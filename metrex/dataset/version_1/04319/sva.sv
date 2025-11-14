// SVA for the provided design. Bind these modules to the DUT without modifying RTL.

// Ripple-carry adder SVA
module rca_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [3:0]  A,
  input  logic [3:0]  B,
  input  logic [3:0]  OUT,
  input  logic [3:0]  sum,
  input  logic        carry
);
  default clocking cb @(posedge clk); endclocking

  // Output mirrors internal sum
  assert property (OUT == sum);

  // After a cycle with reset=1, regs are zeroed
  assert property ($past(reset) |-> (sum == 4'b0 && carry == 1'b0));

  // Main next-state relation (with carry feedback)
  assert property (disable iff (reset)
                   {carry, sum} == $past(A) + $past(B) + $past(carry));

  // No X on registered outputs when not in reset
  assert property (disable iff (reset) !$isunknown({sum, carry, OUT}));

  // Coverage
  cover property ($rose(reset));
  cover property (disable iff (reset) carry);          // carry=1 observed
  cover property (disable iff (reset) !carry);         // carry=0 observed
endmodule

bind ripple_carry_adder rca_sva u_rca_sva (
  .clk(clk), .reset(reset), .A(A), .B(B), .OUT(OUT), .sum(sum), .carry(carry)
);


// Consecutive-ones counter SVA
module coc_sva (
  input  logic        clk,
  input  logic [3:0]  in,
  input  logic [3:0]  out,
  input  logic [3:0]  counter
);
  default clocking cb @(posedge clk); endclocking

  // Output mirrors internal counter
  assert property (out == counter);

  // Functional next-state behavior
  assert property ((in == 4'b0000) |=> counter == 4'b0000);
  assert property ((in == 4'b1111) |=> counter == 4'b1111);
  assert property ((in != 4'b0000 && in != 4'b1111)
                   |=> counter == {$past(counter[2:0]), in[3]});

  // Out is known whenever in is known
  assert property (!$isunknown(in) |-> !$isunknown(out));

  // Coverage: hit each branch and both MSB shift values
  cover property (in == 4'b0000);
  cover property (in == 4'b1111);
  cover property ((in != 4'b0000 && in != 4'b1111) |=> counter[0] == 1'b0);
  cover property ((in != 4'b0000 && in != 4'b1111) |=> counter[0] == 1'b1);
endmodule

bind consecutive_ones_counter coc_sva u_coc_sva (
  .clk(clk), .in(in), .out(out), .counter(counter)
);


// Top-level integration SVA
module top_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [3:0]  A,
  input  logic [3:0]  B,
  input  logic [3:0]  OUT,
  input  logic [3:0]  counter_out,
  input  logic [3:0]  adder_out
);
  default clocking cb @(posedge clk); endclocking

  // OUT is direct pass-through of adder_out
  assert property (OUT == adder_out);

  // End-to-end check: counter reacts correctly to adder_out
  assert property ((adder_out == 4'b0000) |=> counter_out == 4'b0000);
  assert property ((adder_out == 4'b1111) |=> counter_out == 4'b1111);
  assert property ((adder_out != 4'b0000 && adder_out != 4'b1111)
                   |=> counter_out == {$past(counter_out[2:0]), adder_out[3]});

  // Coverage: observe all integration branches and a shift of both MSB values
  cover property (adder_out == 4'b0000);
  cover property (adder_out == 4'b1111);
  cover property ((adder_out != 4'b0000 && adder_out != 4'b1111 && adder_out[3] == 1'b0)
                  |=> counter_out[0] == 1'b0);
  cover property ((adder_out != 4'b0000 && adder_out != 4'b1111 && adder_out[3] == 1'b1)
                  |=> counter_out[0] == 1'b1);
endmodule

bind top_module top_sva u_top_sva (
  .clk(clk), .reset(reset), .A(A), .B(B), .OUT(OUT),
  .counter_out(counter_out), .adder_out(adder_out)
);