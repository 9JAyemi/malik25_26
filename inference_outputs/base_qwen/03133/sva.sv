```systemverilog
module min_max_sva #(
  parameter n = 8
)(
  input [n-1:0] in,
  output reg [n-1:0] min,
  output reg [n-1:0] max
);

  // Sequential logic to update min and max
  always @(posedgeposedge clk or negedge reset_n) begin
    if (!reset_n) begin
      min <= in[0];
      max <= in[0];
    end else begin
      min <= in[0];
      max <= in[0];
      for (integer i = 1; i < n; i = i + 1) begin
        if (in[i] < min) begin
          min <= in[i];
        end
        if (in[i] > max) begin
          max <= in[i];
        end
      end
    end
  end

  // Property to check that min is updated correctly
  property check_min_update;
    @(posedge clk) disable iff (!reset_n) min == in[0] |-> min == in[0];
  endproperty
  check_min_update_inst: assert property (check_min_update) else $error("Min update error");

  // Property to check that max is updated correctly
  property check_max_update;
    @(posedge clk) disable iff (!reset_n) max == in[0] |-> max == in[0];
  endproperty
  check_max_update_inst: assert property (check_max_update) else $error("Max update error");

  // Property to check that min is always less than or equal to max
  property check_min_max_relation;
    @(posedge clk) disable iff (!reset_n) min <= max;
  endproperty
  check_min_max_relation_inst: assert property (check_min_max_relation) else $error("Min greater than max");

  // Property to check that min is updated when a smaller value is found
  property check_min_update_on_smaller_value;
    @(posedge clk) disable iff (!reset_n) $rose(min) |-> $past(min) > in[0];
  endproperty
  check_min_update_on_smaller_value_inst: assert property (check_min_update_on_smaller_value) else $error("Min not updated on smaller value");

  // Property to check that max is updated when a larger value is found
  property check_max_update_on_larger_value;
    @(posedge clk) disable iff (!reset_n) $rose(max) |-> $past(max) < in[0];
  endproperty
  check_max_update_on_larger_value_inst: assert property (check_max_update_on_larger_value) else $error("Max not updated on larger value");

  // Property to check that min and max are updated correctly when all values are the same
  property check_min_max_same_values;
    @(posedge clk) disable iff (!reset_n) in[0] == in[n-1] |-> min == in[0] && max == in[0];
  endproperty
  check_min_max_same_values_inst: assert property (check_min_max_same_values) else $error("Min and max not updated correctly when all values are the same");

  // Property to check that min and max are updated correctly when all values are different
  property check_min_max_different_values;
    @(posedge clk) disable iff (!reset_n) in[0] != in[n-1] |-> min != in[0] && max != in[0];
  endproperty
  check_min_max_different_values_inst: assert property (check_min_max_different_values) else $error("Min and max not updated correctly when all values are different");

  // Property to check that min and max are updated correctly when some values are the same
  property check_min_max_some_same_values;
    @(posedge clk) disable iff (!reset_n) in[0] == in[1] && in[0] != in[2] |-> min == in[0] && max == in[2];
  endproperty
  check_min_max_some_same_values_inst: assert property (check_min_max_some_same_values) else $error("Min and max not updated correctly when some values are the same");

  // Property to check that min and max are updated correctly when some values are the same and others are different
  property check_min_max_some_same_some_different_values;
    @(posedge clk) disable iff (!reset_n) in[0] == in[1] && in[0] != in[2] && in[0] != in[3] |-> min == in[0] && max == in[3];
  endproperty
  check_min_max_some_same_some_different_values_inst: assert property (check_min_max_some_same_some_different_values) else $error("Min and max not updated correctly when some values are the same and others are different");

endmodule
```