// SVA checker for c_incr. Bind this to the DUT.
// Focuses on functional equivalence, slice behavior, and coverage.
module c_incr_sva
  #(parameter int width = 3,
    parameter logic [0:width-1] min_value = '0,
    parameter logic [0:width-1] max_value = (1<<width)-1)
  (input logic [0:width-1] data_in,
   input logic [0:width-1] data_out);

  localparam int unsigned num_values = (max_value - min_value) + 1;
  localparam int unsigned cwidth     = $clog2(num_values);
  localparam bit PWR2                = ((1<<cwidth) == num_values);

  // Sanity on parameters (compile/elab-time)
  initial begin
    assert (min_value <= max_value) else $error("c_incr: min_value > max_value");
    assert (num_values >= 2)        else $error("c_incr: num_values < 2 not supported");
    assert (num_values <= (1<<width)) else $error("c_incr: num_values > 2^width");
  end

  // Sample on any combinational change
  event ev; always @(data_in or data_out) -> ev;
  default clocking cb @ (ev); endclocking

  // Helpers
  localparam int LO_L = (width - cwidth);
  localparam int LO_R = (width - 1);

  function automatic bit in_range(input logic [0:width-1] d);
    return (d >= min_value) && (d <= max_value);
  endfunction

  function automatic logic [0:width-1] ref_next(input logic [0:width-1] d);
    logic [0:width-1] nxt;
    nxt = (d == max_value) ? min_value : (d + 1'b1);
    return nxt;
  endfunction

  function automatic bit lo_carry(input logic [0:width-1] d);
    if (cwidth == 0) return 0;
    return &d[LO_L:LO_R];
  endfunction

  function automatic bit lo_wrap(input logic [0:width-1] d);
    if (cwidth == 0) return 0;
    return (d[LO_L:LO_R] == max_value[LO_L:LO_R]);
  endfunction

  // Golden functional behavior within the specified range
  assert property (in_range(data_in) |-> (data_out == ref_next(data_in)));
  assert property (in_range(data_in) |-> in_range(data_out));

  // LSB slice behavior
  if (cwidth > 0) begin
    if (PWR2) begin
      assert property (in_range(data_in) |-> (data_out[LO_L:LO_R] == (data_in[LO_L:LO_R] + 1'b1)));
    end else begin
      assert property (in_range(data_in) && lo_wrap(data_in)  |-> (data_out[LO_L:LO_R] == min_value[LO_L:LO_R]));
      assert property (in_range(data_in) && !lo_wrap(data_in) |-> (data_out[LO_L:LO_R] == (data_in[LO_L:LO_R] + 1'b1)));
    end
  end

  // MSB slice behavior
  if ((width > cwidth) && (cwidth > 0)) begin : MSB_CHK
    localparam int HI_L = 0;
    localparam int HI_R = (width - cwidth) - 1;
    if (min_value[HI_L:HI_R] == max_value[HI_L:HI_R]) begin
      assert property (in_range(data_in) |-> (data_out[HI_L:HI_R] == data_in[HI_L:HI_R]));
    end else begin
      assert property (in_range(data_in) |-> (data_out[HI_L:HI_R] == (data_in[HI_L:HI_R] + lo_carry(data_in) - lo_wrap(data_in))));
    end
  end

  // Coverage
  cover property (in_range(data_in) && (data_in == min_value) && (data_out == (min_value + 1)));
  cover property (in_range(data_in) && (data_in == max_value) && (data_out == min_value));
  cover property (in_range(data_in) && (data_in >  min_value) && (data_in <  max_value) && (data_out == (data_in + 1)));
  if (cwidth > 0) begin
    cover property (in_range(data_in) && lo_carry(data_in));
    cover property (in_range(data_in) && lo_wrap(data_in));
  end

endmodule

// Bind example:
// bind c_incr c_incr_sva #(.width(width), .min_value(min_value), .max_value(max_value))
//   u_c_incr_sva (.data_in(data_in), .data_out(data_out));