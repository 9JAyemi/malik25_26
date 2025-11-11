module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic        load,
  input logic        up_down,
  input logic [31:0] in,
  input logic [15:0] count,
  input logic [31:0] transition,
  input logic [31:0] prev_in,
  input logic [1:0]  state,
  input logic [7:0]  q
);
  localparam logic [1:0] IDLE=2'b00, DETECT=2'b01, OUTPUT=2'b10;

  function automatic logic [15:0] load_val(input logic [31:0] din);
    return {din[15:12], din[23:20], din[31:28], din[27:24]};
  endfunction

  logic past_valid;
  initial past_valid=1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Reset behavior (next-cycle checks)
  assert property (cb past_valid && $past(reset) |-> (count==16'h0 && state==IDLE && prev_in==32'h0 && transition==32'h0));

  // State encoding legal
  assert property (cb state inside {IDLE, DETECT, OUTPUT});

  // Counter next-state priority and values
  assert property (cb past_valid && !$past(reset) && $past(load) |-> count == load_val($past(in)));
  assert property (cb past_valid && !$past(reset) && !$past(load) && $past(up_down) |-> count == $past(count)+16'd1);
  assert property (cb past_valid && !$past(reset) && !$past(load) && !$past(up_down) |-> count == $past(count)-16'd1);

  // FSM transitions and data-path side-effects
  assert property (cb past_valid && !$past(reset) && $past(state)==IDLE && ($past(in)!=$past(prev_in))
                   |-> state==DETECT && prev_in==$past(in) && transition==$past(transition));
  assert property (cb past_valid && !$past(reset) && $past(state)==IDLE && ($past(in)==$past(prev_in))
                   |-> state==IDLE && prev_in==$past(prev_in) && transition==$past(transition));
  assert property (cb past_valid && !$past(reset) && $past(state)==DETECT && ($past(in)==$past(prev_in))
                   |-> state==IDLE && transition==($past(transition)|$past(prev_in)) && prev_in==$past(prev_in));
  assert property (cb past_valid && !$past(reset) && $past(state)==DETECT && ($past(in)!=$past(prev_in))
                   |-> state==DETECT && prev_in==$past(in) && transition==$past(transition));
  assert property (cb past_valid && !$past(reset) && $past(state)==OUTPUT
                   |-> state==IDLE && prev_in==$past(in) && transition==$past(transition));

  // transition is bitwise-monotonic (only sets bits)
  assert property (cb past_valid && !$past(reset) |-> (transition | $past(transition)) == transition);

  // q mapping (RHS truncation of 48-bit concat -> transition[7:0])
  assert property (cb 1'b1 |-> ##0 (q == transition[7:0]));

  // Coverage
  cover property (cb past_valid && !$past(reset) && $past(load) && count==load_val($past(in)));
  cover property (cb past_valid && !$past(reset) && !$past(load) && $past(up_down) &&
                       $past(count)==16'hFFFF && count==16'h0000); // wrap up
  cover property (cb past_valid && !$past(reset) && !$past(load) && !$past(up_down) &&
                       $past(count)==16'h0000 && count==16'hFFFF); // wrap down
  cover property (cb past_valid && !$past(reset) && $past(state)==DETECT && ($past(in)==$past(prev_in)) &&
                       transition != $past(transition)); // OR update
  cover property (cb past_valid && !$past(reset) && $past(state)==DETECT && ($past(in)!=$past(prev_in)) ##1
                       state==DETECT && (in!=prev_in)); // linger in DETECT
  cover property (cb state==OUTPUT); // likely unreachable in this RTL
  cover property (cb transition!=32'h0 && q==transition[7:0]);

endmodule

bind top_module top_module_sva sva(
  .clk(clk),
  .reset(reset),
  .load(load),
  .up_down(up_down),
  .in(in),
  .count(count),
  .transition(transition),
  .prev_in(prev_in),
  .state(state),
  .q(q)
);