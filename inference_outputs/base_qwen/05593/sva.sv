```systemverilog
module binary_counter_sva (
  input logic s_aclk,
  input logic AR,
  input logic E,
  output logic [3:0] Q
);
  // Counter reset behavior
  reset: assert property (
    @(posedge s_aclk) disable iff (!AR) (AR |-> Q == 4'b0)
  );

  // Counter increment behavior
  increment: assert property (
    @(posedge s_aclk) disable iff (!AR) (E |-> (Q == 4'b1111) ? Q == 4'b0 : Q + 1 == Q)
  );

  // Counter does not increment when AR is set
  no_increment_on_reset: assert property (
    @(posedge s_aclk) disable iff (!AR) (!AR |-> !E |-> Q == Q)
  );

  // Counter does not reset when E is set
  no_reset_on_increment: assert property (
    @(posedge s_aclk) disable iff (!AR) (E |-> !AR |-> Q == Q)
  );

  // Counter wraps around at 15
  wrap_around: assert property (
    @(posedge s_aclk) disable iff (!AR) (Q == 4'b1111 |-> Q + 1 == 4'b0)
  );

  // Counter does not wrap around when AR is set
  no_wrap_around_on_reset: assert property (
    @(posedge s_aclk) disable iff (!AR) (!AR |-> Q == Q)
  );

  // Counter does not increment when E is not set
  no_increment_without_enable: assert property (
    @(posedge s_aclk) disable iff (!AR) (!E |-> Q == Q)
  );

  // Counter does not reset when AR is not set
  no_reset_without_reset: assert property (
    @(posedge s_aclk) disable iff (!AR) (!AR |-> Q == Q)
  );

  // Counter does not wrap around when E is not set
  no_wrap_around_without_enable: assert property (
    @(posedge s_aclk) disable iff (!AR) (!E |-> Q == Q)
  );

  // Counter does not increment when AR is set
  no_increment_on_reset: assert property (
    @(posedge s_aclk) disable iff (!AR) (!AR |-> !E |-> Q == Q)
  );

  // Counter does not reset when E is set
  no_reset_on_increment: assert property (
    @(posedge s_aclk) disable iff (!AR) (E |-> !AR |-> Q == Q)
  );
endmodule
```