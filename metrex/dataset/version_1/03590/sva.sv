// SVA for clk_divider. Bind this to the DUT.
// Focus: functional correctness and concise coverage.

module clk_divider_sva #(
  parameter string ena_register_mode = "always enabled"
)(
  input  logic inclk,
  input  logic ena,
  input  logic enaout,
  input  logic outclk
);

  default clocking cb @(posedge inclk); endclocking

  // Track availability of $past()
  logic past_valid;
  initial past_valid = 0;
  always @(posedge inclk) past_valid <= 1'b1;

  // Core outclk functional relation to ena and prior outclk state
  // new_outclk == (ena ? ~old_outclk : 1'b0)
  assert property (past_valid |-> (outclk == (ena ? !$past(outclk) : 1'b0)));

  // Any change of outclk must occur only when ena is 1
  assert property (past_valid && (outclk != $past(outclk)) |-> ena);

  // When ena is 0, outclk must be 0 at this cycle
  assert property (past_valid && !ena |-> outclk == 1'b0);

  // No X on outputs after first observed cycle
  assert property (past_valid |-> !$isunknown({outclk, enaout}));

  // Mode-specific checks for enaout
  localparam bit MODE_ALWAYS = (ena_register_mode == "always enabled");
  localparam bit MODE_SYNC   = (ena_register_mode == "synchronous");
  localparam bit MODE_ASYNC  = (ena_register_mode == "asynchronous");

  generate
    if (MODE_ALWAYS) begin
      // After first cycle, enaout must be permanently 1
      assert property (past_valid |-> enaout == 1'b1);
      // Cover: stable high for a few cycles
      cover property (past_valid ##1 enaout[*3]);
    end
    if (MODE_SYNC) begin
      // Registered copy of ena
      assert property (past_valid |-> enaout == $past(ena));
      // Edge alignment (1-cycle latency)
      assert property (past_valid && $rose(ena) |-> $rose(enaout));
      assert property (past_valid && $fell(ena) |-> $fell(enaout));
      // Coverage
      cover property (past_valid && $rose(ena) ##1 $rose(enaout));
      cover property (past_valid && $fell(ena) ##1 $fell(enaout));
    end
    if (MODE_ASYNC) begin
      // Sticky-high OR behavior
      assert property (past_valid |-> enaout == ($past(enaout) | ena));
      // Monotonic: once high, never falls
      assert property (past_valid && $past(enaout) |-> enaout);
      // Coverage: first rise caused by ena
      cover property (past_valid && !$past(enaout) && $rose(ena) ##0 enaout);
    end
  endgenerate

  // Outclk coverage: see both polarities under enable, and forced-low on disable
  cover property (past_valid && ena && $rose(outclk));
  cover property (past_valid && ena && $fell(outclk));
  cover property (past_valid && $past(ena) && !ena && $past(outclk) && !outclk);

endmodule

// Bind example:
// bind clk_divider clk_divider_sva #(.ena_register_mode(ena_register_mode))
//   clk_divider_sva_i (.inclk(inclk), .ena(ena), .enaout(enaout), .outclk(outclk));