// SVA for the provided design. Concise, high-signal-value checks with key coverage.

// Top-level checks
module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic        select,
  input logic [3:1]  ena,
  input logic [15:0] q,
  input logic [99:0] sum,
  input logic [15:0] bcd_out,
  input logic        cout
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  a_top_reset_q:   assert property (reset |-> q   == 16'h0000);
  a_top_reset_ena: assert property (reset |-> ena == 3'b000);

  // Datapath select behavior and enables
  a_bcd_path: assert property (disable iff (reset) select  |-> (ena == 3'b000 && q == bcd_out));
  a_sum_path: assert property (disable iff (reset) !select |-> (ena == 3'b111 && q == sum[15:0]));

  // Outputs sane after reset
  a_no_x_out: assert property (disable iff (reset) !$isunknown({ena,q}));

  // Coverage: exercise both paths, switching, adder carry, and counter rollover
  c_sel0:     cover property (disable iff (reset) !select);
  c_sel1:     cover property (disable iff (reset)  select);
  c_switch01: cover property (disable iff (reset)  select ##1 !select);
  c_switch10: cover property (disable iff (reset) !select ##1  select);
  c_cout:     cover property (disable iff (reset) cout);
  c_roll:     cover property (disable iff (reset) bcd_out == 16'hFFFF ##1 bcd_out == 16'h0000);
endmodule

bind top_module top_module_sva u_top_sva (
  .clk(clk), .reset(reset), .select(select),
  .ena(ena), .q(q),
  .sum(sum), .bcd_out(bcd_out), .cout(cout)
);


// BCD counter checks (binary up-counter as coded)
module bcd_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [15:0] bcd_out
);
  default clocking cb @(posedge clk); endclocking

  a_cnt_reset: assert property (reset |-> bcd_out == 16'h0000);
  a_cnt_inc:   assert property (disable iff (reset) bcd_out == $past(bcd_out) + 16'd1);
  a_cnt_nox:   assert property (disable iff (reset) !$isunknown(bcd_out));

  c_cnt_roll:  cover property (disable iff (reset) bcd_out == 16'hFFFF ##1 bcd_out == 16'h0000);
endmodule

bind bcd_counter bcd_counter_sva u_cnt_sva (.clk(clk), .reset(reset), .bcd_out(bcd_out));


// CLA checks (functional equivalence and clean outputs when inputs are known)
module carry_lookahead_adder_sva (
  input  logic [99:0] a, b,
  input  logic        cin,
  input  logic [99:0] sum,
  input  logic        cout
);
  logic [100:0] full_add;
  always @* begin
    full_add = {1'b0, a} + {1'b0, b} + cin;
    if (!$isunknown({a,b,cin})) begin
      assert ({cout, sum} == full_add)
        else $error("CLA mismatch: {cout,sum} != a+b+cin");
      assert (!$isunknown({cout,sum}))
        else $error("CLA outputs contain X/Z with known inputs");
    end
  end
endmodule

bind carry_lookahead_adder carry_lookahead_adder_sva u_cla_sva (
  .a(a), .b(b), .cin(cin), .sum(sum), .cout(cout)
);