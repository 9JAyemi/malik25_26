// SVA for rising_edge_detector: concise, quality-focused
// Bindable checker that verifies pipeline shifting, functional spec, reset behavior, X-prop, and covers detection

module red_checker #(parameter W=32) (
  input  logic            clk,
  input  logic            reset,
  input  logic [W-1:0]    in,
  input  logic [W-1:0]    out,
  // tap internals for stronger checks
  input  logic [W-1:0]    p0,
  input  logic [W-1:0]    p1,
  input  logic [W-1:0]    p2
);
  default clocking cb @(posedge clk); endclocking

  // history-valid flags to avoid $past depth issues after reset
  logic ok1, ok2;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      ok1 <= 1'b0;
      ok2 <= 1'b0;
    end else begin
      ok1 <= 1'b1;
      ok2 <= ok1;
    end
  end

  // Reset clears
  assert property (reset |=> (out=='0 && p0=='0 && p1=='0 && p2=='0))
    else $error("Reset did not clear state/outputs");

  // Pipeline shifting (internal consistency)
  assert property (ok1 |-> (p0 == $past(in)))
    else $error("pipeline_reg[0] does not track in");
  assert property (ok1 |-> ({p2,p1} == $past({p1,p0})))
    else $error("pipeline_reg shift chain broken");

  // Functional spec: out == in[t-2] & ~in[t-1] & in[t]
  assert property (ok2 |-> (out == ($past(in,2) & ~$past(in,1) & in)))
    else $error("Output not equal to 3-sample 101 pattern");

  // No unknowns on out when contributing inputs are known
  assert property (ok2 && !$isunknown({in, $past(in,1), $past(in,2)} ) |-> !$isunknown(out))
    else $error("Unknown X/Z on out with known inputs/history");

  // Coverage: at least one detect, and an explicit 101 detect on bit 0
  cover property (ok2 && (|out));
  cover property (in[0] ##1 !in[0] ##1 (in[0] && out[0]));

endmodule

// Bind into DUT
bind rising_edge_detector red_checker #(.W(32)) u_red_checker (
  .clk(clk),
  .reset(reset),
  .in(in),
  .out(out),
  .p0(pipeline_reg[0]),
  .p1(pipeline_reg[1]),
  .p2(pipeline_reg[2])
);