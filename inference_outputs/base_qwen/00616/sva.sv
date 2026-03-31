```systemverilog
module FFType_assertions (
  input logic clock,
  input logic reset,
  input logic io_in,
  input logic io_init,
  output logic io_out,
  input logic io_enable
);
  // io_out should always be equal to d
  io_out_valid: assert property (
    @(posedge clock) disable iff (!reset) io_out == d
  );

  // d should be assigned io_init at reset
  reset_assignment: assert property (
    @(posedge clock) disable iff (!reset) reset |-> d == io_init
  );

  // d should be assigned io_in when io_enable is high
  enable_assignment: assert property (
    @(posedge clock) disable iff (!reset) io_enable |-> d == io_in
  );

  // io_out should not change when reset is high
  reset_stability: assert property (
    @(posedge clock) disable iff (reset) io_out == io_out
  );

  // io_out should not change when io_enable is low
  enable_stability: assert property (
    @(posedge clock) disable iff (!reset) !io_enable |-> io_out == io_out
  );

  // io_out should not change when io_in is not changing
  input_stability: assert property (
    @(posedge clock) disable iff (!reset) io_in == io_in |-> io_out == io_out
  );

  // io_out should not change when io_init is not changing
  init_stability: assert property (
    @(posedge clock) disable iff (!reset) io_init == io_init |-> io_out == io_out
  );

  // io_out should not change when io_enable is not changing
  enable_stability_2: assert property (
    @(posedge clock) disable iff (!reset) io_enable == io_enable |-> io_out == io_out
  );

  // io_out should not change when io_in is not changing
  input_stability_2: assert property (
    @(posedge clock) disable iff (!reset) io_in == io_in |-> io_out == io_out
  );

  // io_out should not change when io_init is not changing
  init_stability_2: assert property (
    @(posedge clock) disable iff (!reset) io_init == io_init |-> io_out == io_out
  );
endmodule
```