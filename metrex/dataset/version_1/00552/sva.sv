// SVA for d_ff_en_parameterized — concise, high-quality checks and coverage

module d_ff_en_parameterized_sva #(
  parameter int WIDTH = 1,
  parameter logic [WIDTH-1:0] INIT = '0
)(
  input  logic                CLK,
  input  logic                E,
  input  logic [WIDTH-1:0]    D,
  input  logic [WIDTH-1:0]    Q
);

  default clocking cb @(posedge CLK); endclocking

  // Track first sampled cycle to guard $past()
  logic started;
  initial started = 1'b0;
  always @(posedge CLK) started <= 1'b1;

  // Controls must be known
  assert property (@cb !$isunknown(E))
    else $error("E is X/Z at CLK edge");

  // When enabled, data must be known
  assert property (@cb E |-> !$isunknown(D))
    else $error("D is X/Z while E=1 at CLK edge");

  // Functional correctness
  assert property (@cb disable iff (!started) E |=> (Q == $past(D)))
    else $error("Q != prior D when E=1");

  assert property (@cb disable iff (!started) !E |=> (Q == $past(Q)))
    else $error("Q did not hold value when E=0");

  // Any Q change must be due to enable and reflect prior D
  assert property (@cb disable iff (!started) (Q != $past(Q)) |-> ($past(E) && (Q == $past(D))))
    else $error("Q changed without E=1 and matching prior D");

  // Initialization check
  initial begin
    assert (Q === INIT) else $error("Initial Q (%0h) != INIT (%0h)", Q, INIT);
    cover  (Q === INIT);
  end

  // Coverage: enable update and disable hold (with D toggling)
  cover property (@cb disable iff (!started) E ##1 (Q != $past(Q)));
  cover property (@cb disable iff (!started) !E && (D != $past(D)) ##1 (Q == $past(Q)));

endmodule

// Bind into DUT
bind d_ff_en_parameterized
  d_ff_en_parameterized_sva #(.WIDTH(WIDTH), .INIT(INIT)) d_ff_en_parameterized_sva_i (.CLK(CLK), .E(E), .D(D), .Q(Q));