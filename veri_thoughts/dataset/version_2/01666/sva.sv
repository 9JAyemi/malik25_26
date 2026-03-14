module floating_point_arithmetic_sva (
  input logic [31:0] a,
  input logic [31:0] b,
  input logic [1:0]  ctrl,
  input logic [31:0] result
);
  // No clock/reset in RTL; use $global_clock for synchronous SVA.

  // Local reference computations matching RTL arithmetic/truncation
  logic [31:0] add_ref, sub_ref, mul_ref, div_ref;
  always_comb begin
    add_ref = a + b;
    sub_ref = a - b;
    mul_ref = a * b;
    div_ref = a / b;
  end

  ///// Operation select /////
  // ctrl==00 selects addition
  check_select_add: assert property (
    @(posedge $global_clock) (ctrl == 2'b00) |-> (result == add_ref)
  );
  // ctrl==01 selects subtraction
  check_select_sub: assert property (
    @(posedge $global_clock) (ctrl == 2'b01) |-> (result == sub_ref)
  );
  // ctrl==10 selects multiplication (truncated to 32b)
  check_select_mul: assert property (
    @(posedge $global_clock) (ctrl == 2'b10) |-> (result == mul_ref)
  );
  // ctrl==11 selects division when divisor is nonzero
  check_select_div_no_div0: assert property (
    @(posedge $global_clock) (ctrl == 2'b11 && b != 32'd0) |-> (result == div_ref)
  );

  ///// Identities and corner cases consistent with the RTL arithmetic /////
  // Adding zero on A returns B
  check_add_identity_a_zero: assert property (
    @(posedge $global_clock) (ctrl == 2'b00 && a == 32'd0) |-> (result == b)
  );
  // Adding zero on B returns A
  check_add_identity_b_zero: assert property (
    @(posedge $global_clock) (ctrl == 2'b00 && b == 32'd0) |-> (result == a)
  );
  // Subtracting zero returns A
  check_sub_identity_b_zero: assert property (
    @(posedge $global_clock) (ctrl == 2'b01 && b == 32'd0) |-> (result == a)
  );
  // Subtracting a from itself yields zero
  check_sub_self_zero: assert property (
    @(posedge $global_clock) (ctrl == 2'b01 && a == b) |-> (result == 32'd0)
  );
  // Multiplication by zero yields zero
  check_mul_zero_absorb: assert property (
    @(posedge $global_clock) (ctrl == 2'b10 && (a == 32'd0 || b == 32'd0)) |-> (result == 32'd0)
  );
  // Multiplication identity with one on A
  check_mul_identity_a_one: assert property (
    @(posedge $global_clock) (ctrl == 2'b10 && a == 32'd1) |-> (result == b)
  );
  // Multiplication identity with one on B
  check_mul_identity_b_one: assert property (
    @(posedge $global_clock) (ctrl == 2'b10 && b == 32'd1) |-> (result == a)
  );
  // Division identity by one
  check_div_identity_b_one: assert property (
    @(posedge $global_clock) (ctrl == 2'b11 && b == 32'd1) |-> (result == a)
  );
  // Zero dividend yields zero when divisor nonzero
  check_div_zero_numerator: assert property (
    @(posedge $global_clock) (ctrl == 2'b11 && a == 32'd0 && b != 32'd0) |-> (result == 32'd0)
  );

  ///// Combinational stability /////
  // If inputs and ctrl are stable, result remains stable
  check_result_stable_when_inputs_stable: assert property (
    @(posedge $global_clock) ($stable(a) && $stable(b) && $stable(ctrl)) |-> $stable(result)
  );
endmodule