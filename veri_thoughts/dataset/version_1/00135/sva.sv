// SVA for bitwise_and
module bitwise_and_sva #(parameter WIDTH=16)
(
  input  logic [WIDTH-1:0] data_in,
  input  logic [WIDTH-1:0] mask,
  input  logic             enable,
  input  logic [WIDTH-1:0] data_out
);

  // Functional correctness on any input change (allow 0-delay settle)
  property p_func;
    @(data_in or mask or enable)
      (!$isunknown({enable, data_in, mask})) |-> ##0
        (data_out == (enable ? (data_in & mask) : data_in));
  endproperty
  assert property (p_func);

  // No X/Z on output when inputs are known
  property p_no_x_out;
    @(data_in or mask or enable)
      (!$isunknown({enable, data_in, mask})) |-> ##0
        (!$isunknown(data_out));
  endproperty
  assert property (p_no_x_out);

  // Coverage: enable edges and key mask cases
  cover property (@(data_in or mask or enable) $rose(enable));
  cover property (@(data_in or mask or enable) $fell(enable));

  // Pass-through when disabled and data changes
  cover property (@(data_in or mask or enable) ##0
                  (!enable && $changed(data_in) && data_out == data_in));

  // All-zero mask produces zero output when enabled
  cover property (@(data_in or mask or enable) ##0
                  (enable && (mask == {WIDTH{1'b0}}) && (|data_in) && (data_out == {WIDTH{1'b0}})));

  // All-one mask equals pass-through when enabled
  cover property (@(data_in or mask or enable) ##0
                  (enable && (mask == {WIDTH{1'b1}}) && (data_out == data_in)));

  // Mixed mask exercising both 0- and 1-masked bits
  cover property (@(data_in or mask or enable) ##0
                  (enable &&
                   (|(mask & data_in)) && (|((~mask) & data_in)) &&
                   (data_out == (data_in & mask))));

endmodule

// Bind into DUT
bind bitwise_and bitwise_and_sva #(.WIDTH(16)) u_bitwise_and_sva (.*);