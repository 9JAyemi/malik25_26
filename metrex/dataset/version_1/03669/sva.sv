// SVA for acl_fp_custom_add_op
// Bind this module to the DUT instance
module acl_fp_custom_add_op_sva #(
  parameter HIGH_CAPACITY = 1
)(
  input  logic               clock,
  input  logic               resetn,
  input  logic [26:0]        left_mantissa,
  input  logic [26:0]        right_mantissa,
  input  logic               left_sign,
  input  logic               right_sign,
  input  logic [8:0]         common_exponent,
  input  logic               valid_in,
  input  logic               stall_in,
  input  logic               enable,

  input  logic [27:0]        resulting_mantissa,
  input  logic [8:0]         resulting_exponent,
  input  logic               resulting_sign,
  input  logic               valid_out,
  input  logic               stall_out
);

  // Expected adder/subtractor (two's complement subtract when signs differ)
  function automatic logic [27:0] addsub(input bit do_sub,
                                         input logic [26:0] L,
                                         input logic [26:0] R);
    logic [27:0] L28, R28;
    L28 = {1'b0, L};
    R28 = {1'b0, R};
    addsub = L28 + (do_sub ? (~R28 + 28'd1) : R28);
  endfunction

  // Basic interface/known checks
  // stall_out must equal valid_out & stall_in
  assert property (@(posedge clock) stall_out == (valid_out & stall_in));

  // During reset active-low, valid_out must be 0; after reset deassert, outputs never X
  assert property (@(posedge clock) !resetn |-> (valid_out == 1'b0));
  assert property (@(posedge clock) disable iff (!resetn)
                   !$isunknown({resulting_mantissa, resulting_exponent, resulting_sign, valid_out, stall_out}));

  // Core pipeline behavior
  generate
    if (HIGH_CAPACITY) begin : g_hicap
      // Hold on stall (valid_out && stall_in), otherwise update
      assert property (@(posedge clock) disable iff (!resetn)
                       (valid_out && stall_in) |=> $stable({resulting_mantissa, resulting_exponent, resulting_sign, valid_out}));

      assert property (@(posedge clock) disable iff (!resetn)
                       (!(valid_out && stall_in)) |=> (
                         (valid_out == $past(valid_in)) &&
                         (resulting_mantissa == addsub($past(left_sign) ^ $past(right_sign),
                                                       $past(left_mantissa), $past(right_mantissa))) &&
                         (resulting_exponent == $past(common_exponent)) &&
                         (resulting_sign == $past(left_sign))
                       ));
    end else begin : g_lowcap
      // Gated by 'enable'
      assert property (@(posedge clock) disable iff (!resetn)
                       (!enable) |=> $stable({resulting_mantissa, resulting_exponent, resulting_sign, valid_out}));

      assert property (@(posedge clock) disable iff (!resetn)
                       (enable) |=> (
                         (valid_out == $past(valid_in)) &&
                         (resulting_mantissa == addsub($past(left_sign) ^ $past(right_sign),
                                                       $past(left_mantissa), $past(right_mantissa))) &&
                         (resulting_exponent == $past(common_exponent)) &&
                         (resulting_sign == $past(left_sign))
                       ));
    end
  endgenerate

  // Functional cover: exercise add, sub, stall/hold, and stall release
  generate
    if (HIGH_CAPACITY) begin
      cover property (@(posedge clock) disable iff (!resetn)
                      (!(valid_out && stall_in) && (left_sign ^ right_sign) == 1'b0));
      cover property (@(posedge clock) disable iff (!resetn)
                      (!(valid_out && stall_in) && (left_sign ^ right_sign) == 1'b1));
      cover property (@(posedge clock) disable iff (!resetn)
                      (valid_out && stall_in)[*2]);
      cover property (@(posedge clock) disable iff (!resetn)
                      (valid_out && stall_in) ##1 (!stall_in) ##1 (!stall_out && valid_out));
    end else begin
      cover property (@(posedge clock) disable iff (!resetn) (enable && (left_sign ^ right_sign) == 1'b0));
      cover property (@(posedge clock) disable iff (!resetn) (enable && (left_sign ^ right_sign) == 1'b1));
      cover property (@(posedge clock) disable iff (!resetn) (!enable) ##1 enable);
    end
  endgenerate

endmodule

// Bind to DUT
bind acl_fp_custom_add_op
  acl_fp_custom_add_op_sva #(.HIGH_CAPACITY(HIGH_CAPACITY)) i_acl_fp_custom_add_op_sva (
    .clock(clock),
    .resetn(resetn),
    .left_mantissa(left_mantissa),
    .right_mantissa(right_mantissa),
    .left_sign(left_sign),
    .right_sign(right_sign),
    .common_exponent(common_exponent),
    .valid_in(valid_in),
    .stall_in(stall_in),
    .enable(enable),
    .resulting_mantissa(resulting_mantissa),
    .resulting_exponent(resulting_exponent),
    .resulting_sign(resulting_sign),
    .valid_out(valid_out),
    .stall_out(stall_out)
  );