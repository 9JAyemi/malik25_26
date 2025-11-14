// SVA for simple_calculator
// Bind this module to the DUT
module simple_calculator_sva(
  input logic [7:0] a, b,
  input logic [3:0] control,
  input logic [7:0] result
);

  // Clockless concurrent assertions using the global clock
  default clocking @(posedge $global_clock); endclocking

  localparam logic [3:0] ADD=4'b0000, SUB=4'b0001, MUL=4'b0010, DIV=4'b0011;

  // Basic input sanity
  ap_inputs_known: assert property (!$isunknown({a,b,control}));

  // Functional correctness (mod-256 where applicable)
  ap_add: assert property (control==ADD |-> result == (a + b)[7:0]);
  ap_sub: assert property (control==SUB |-> result == (a - b)[7:0]);
  ap_mul: assert property (control==MUL |-> result == (a * b)[7:0]);
  ap_div_ok: assert property ((control==DIV && b!=0) |-> result == (a / b));
  ap_div0_x: assert property ((control==DIV && b==0) |-> $isunknown(result));
  ap_default_zero: assert property (!(control inside {ADD,SUB,MUL,DIV}) |-> result == 8'h00);

  // Result must be known in all cases except div-by-zero
  ap_no_x: assert property ((control!=DIV || b!=0) |-> !$isunknown(result));

  // Stability: if inputs/control don't change, result must not change
  ap_stable: assert property ($stable(a) && $stable(b) && $stable(control) |=> $stable(result));

  // Coverage: exercise all modes and key corner cases
  cp_add:        cover property (control==ADD);
  cp_sub:        cover property (control==SUB);
  cp_mul:        cover property (control==MUL);
  cp_div_ok:     cover property (control==DIV && b!=0);
  cp_div0:       cover property (control==DIV && b==0);
  cp_default:    cover property (!(control inside {ADD,SUB,MUL,DIV}));

  // Corner cases
  cp_add_ovf:    cover property (control==ADD && (a + b) > 8'hFF);
  cp_sub_borrow: cover property (control==SUB && a < b);
  cp_mul_ovf:    cover property (control==MUL && (a * b) > 8'hFF);
  cp_div_rem:    cover property (control==DIV && b!=0 && (a % b) != 0);

endmodule

// Bind into the DUT
bind simple_calculator simple_calculator_sva u_simple_calculator_sva(
  .a(a),
  .b(b),
  .control(control),
  .result(result)
);