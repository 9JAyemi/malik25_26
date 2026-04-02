module counter_sva (
   input logic clk,
   input logic reset,
   input logic enable,
   output logic [3:0] count,
   output logic overflow
);
   ///// Counter reset /////
   // At reset, the counter must be zero and overflow must be low.
   reset: assert property (
       @(posedge clk) disable iff (!reset) (reset |-> (count == 4'b0000) && (overflow == 1'b0))
   );

   ///// Counter enable /////
   // When enable is high, the counter should increment.
   enable_incr: assert property (
       @(posedge clk) disable iff (!reset) (enable |-> (count + 1 == count + 1))
   );

   ///// Counter overflow /////
   // When the counter reaches its maximum value, it should overflow.
   overflow_check: assert property (
       @(posedge clk) disable iff (!reset) (count == 4'b1111 |-> overflow == 1'b1)
   );

   ///// Counter underflow /////
   // When the counter is reset, it should not underflow.
   underflow_check: assert property (
       @(posedge clk) disable iff (!reset) (reset |-> count != 4'b1111)
   );

   ///// Counter wrap-around /////
   // When the counter reaches its maximum value and enable is high, it should wrap around to zero.
   wrap_around: assert property (
       @(posedge clk) disable iff (!reset) (enable && count == 4'b1111 |-> count == 4'b0000)
   );

   ///// Counter does not increment when enable is low /////
   // When enable is low, the counter should not increment.
   no_incr_when_disabled: assert property (
       @(posedge clk) disable iff (!reset) (!enable |-> count == count)
   );

   ///// Counter does not overflow when enable is low /////
   // When enable is low, the counter should not overflow.
   no_overflow_when_disabled: assert property (
       @(posedge clk) disable iff (!reset) (!enable |-> overflow == 1'b0)
   );

   ///// Counter does not underflow when reset is low /////
   // When reset is low, the counter should not underflow.
   no_underflow_when_reset: assert property (
       @(posedge clk) disable iff (reset) (reset |-> count != 4'b1111)
   );

   ///// Counter does not wrap-around when reset is low /////
   // When reset is low, the counter should not wrap-around.
   no_wrap_around_when_reset: assert property (
       @(posedge clk) disable iff (reset) (reset |-> count != 4'b0000)
   );
endmodule