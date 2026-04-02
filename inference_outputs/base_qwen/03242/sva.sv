module counter_4bit_sva (
  input logic clk,
  input logic reset,
  input logic enable,
  output logic [3:0] count
);

  always @(posedge clk) begin
    // Reset behavior: count should be 0 when reset is asserted
    reset_behavior: assert property (
      disable iff (!reset) reset |-> (count == 4'b0)
    );
  end

  always @(posedge clk) begin
    // Enable behavior: count should increment when enable is asserted and reset is not asserted
    enable_behavior: assert property (
      disable iff (!reset) enable |-> (count == count_reg + 1)
    );
  end

  always @(posedge clk) begin
    // Count register should not change when reset is asserted
    count_reg_reset: assert property (
      disable iff (!reset) reset |-> (count_reg == 4'b0)
    );
  end

  always @(posedge clk) begin
    // Count register should increment when enable is asserted and reset is not asserted
    count_reg_enable: assert property (
      disable iff (!reset) enable |-> (count_reg == count_reg + 1)
    );
  end

  always @(posedge clk) begin
    // Count should be a 4-bit value
    count_width: assert property (
      disable iff (!reset) count |-> (count inside {[0:15]})
    );
  end

  always @(posedge clk) begin
    // Count register should not change when enable is not asserted and reset is not asserted
    count_reg_no_enable: assert property (
      disable iff (!reset) !enable |-> (count_reg == count_reg)
    );
  end

  always @(posedge clk) begin
    // Count should not change when reset is not asserted
    count_no_reset: assert property (
      disable iff (!reset) !reset |-> (count == count_reg)
    );
  end

  always @(posedge clk) begin
    // Count register should be 0 when reset is asserted
    count_reg_reset_value: assert property (
      disable iff (!reset) reset |-> (count_reg == 4'b0)
    );
  end

  always @(posedge clk) begin
    // Count should be a 4-bit value
    count_value: assert property (
      disable iff (!reset) count |-> (count inside {[0:15]})
    );
  end

endmodule