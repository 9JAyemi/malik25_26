// SVA for binary_subtractor/adder/top_module
// Bind-friendly, concise, focused on key checks and coverage.

module adder_sva (input [7:0] a, b, input [8:0] sum);
  // Functional correctness of combinational adder
  always_comb begin
    assert (#0 (sum == ({1'b0,a} + {1'b0,b})))
      else $error("Adder sum mismatch");
  end
endmodule

module binary_subtractor_sva (input [7:0] a, b, input [8:0] diff);
  // Internal structure/functional checks
  // b_not is internal to binary_subtractor; visible when bound.
  // adder_inst is the internal adder instance.
  // 1) b_not correctness
  always_comb assert (#0 (b_not == ~b)) else $error("b_not != ~b");
  // 2) Connectivity to adder
  always_comb assert (#0 (adder_inst.a == a && adder_inst.b == b_not))
    else $error("Adder connectivity mismatch");
  // 3) Implemented diff is bitwise AND of zero-extended a and ~b
  always_comb assert (#0 (diff == ({1'b0,a} & {1'b0,b_not})))
    else $error("diff != ({1'b0,a} & {1'b0,~b})");
  // 4) MSB of diff must be 0 due to zero-extend-and-AND
  always_comb assert (#0 (diff[8] == 1'b0)) else $error("diff[8] must be 0");

  // Lightweight functional coverage of interesting corners (combinational sampling)
  // These use immediate cover to keep things simple and tool-friendly.
  always_comb begin
    cover ({a,b} == 16'h0000);               // both zero
    cover ({a,b} == 16'hFF00);               // a=FF, b=00
    cover ({a,b} == 16'h00FF);               // a=00, b=FF
    cover ({a,b} == {a,a});                  // a==b
    cover ((adder_inst.sum[8]) == 1'b1);     // adder carry-out occurs
  end
endmodule

module top_module_sva (
  input clk, input reset,
  input [7:0] a, b,
  input [8:0] diff
);
  // Bound inside top_module; diff_wire and sub_inst are visible.
  default clocking cb @(posedge clk); endclocking

  // Reset behavior: registered output set to 9'b000000001 on reset
  property p_reset_value;
    reset |=> (diff == 9'b000000001);
  endproperty
  assert property (p_reset_value) else $error("Reset value mismatch for diff");

  // Registering behavior: diff follows diff_wire on next cycle when not in reset
  property p_reg_follow;
    !reset |=> (diff == $past(diff_wire));
  endproperty
  assert property (p_reg_follow) else $error("diff does not follow diff_wire");

  // Implementation equivalence: diff reflects zero-extended (a & ~b) one cycle later
  property p_impl_equiv;
    !reset |=> (diff == ($past({1'b0,a} & {1'b0,~b})));
  endproperty
  assert property (p_impl_equiv) else $error("Top impl mismatch vs a & ~b");

  // Optional intended behavior: two's-complement subtraction a - b into 9 bits
  // Enable to check spec vs implementation; likely to fail with current RTL.
  localparam bit CHECK_INTENT = 1'b1;
  generate if (CHECK_INTENT) begin
    property p_intended_sub;
      !reset |=> (diff == ($past({1'b0,a}) - $past({1'b0,b})));
    endproperty
    assert property (p_intended_sub)
      else $error("Spec mismatch: diff != a - b (registered)");
  end endgenerate

  // Coverage: reset sequence, carry in adder, and edge input patterns
  cover property (reset ##1 !reset);                                 // exit reset
  cover property (!reset and sub_inst.adder_inst.sum[8]);            // adder carry-out observed
  cover property (!reset and (a==8'h00) and (b==8'hFF));             // min-max
  cover property (!reset and (a==8'hFF) and (b==8'h00));             // max-min
  cover property (!reset and (a==b));                                // equal operands
  cover property (!reset and (diff==9'h000));                        // zero diff observed
endmodule

// Binds
bind adder             adder_sva               u_adder_sva      (.a(a), .b(b), .sum(sum));
bind binary_subtractor binary_subtractor_sva   u_subtractor_sva (.a(a), .b(b), .diff(diff));
bind top_module        top_module_sva          u_top_sva        (.clk(clk), .reset(reset), .a(a), .b(b), .diff(diff));