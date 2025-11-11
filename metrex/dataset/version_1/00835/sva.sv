// SVA checker for zipdiv. Bind this to the DUT.
// Focus: protocol, bounded progress, functional correctness, key micro-steps, and flags.

module zipdiv_sva
  #(parameter int BW=32, LGBW=5)
(
  input  logic                 i_clk, i_reset,
  input  logic                 i_wr, i_signed,
  input  logic [BW-1:0]        i_numerator, i_denominator,
  input  logic                 o_busy, o_valid, o_err,
  input  logic [BW-1:0]        o_quotient,
  input  logic [3:0]           o_flags,

  // Internal DUT signals (bound)
  input  logic                 r_busy,
  input  logic [2*BW-2:0]      r_divisor,
  input  logic [BW-1:0]        r_dividend,
  input  logic                 r_sign, pre_sign, r_z, r_c, last_bit,
  input  logic [LGBW-1:0]      r_bit,
  input  logic                 zero_divisor
);

  // Derived
  logic [BW:0] diff;
  assign diff = r_dividend - r_divisor[BW-1:0];

  // Capture operands at start
  logic                 s_valid, s_signed;
  logic [BW-1:0]        s_num, s_den;
  always_ff @(posedge i_clk) begin
    if (i_reset || o_valid) begin
      s_valid  <= 1'b0;
      s_signed <= 1'b0;
      s_num    <= '0;
      s_den    <= '0;
    end else if (i_wr) begin
      s_valid  <= 1'b1;
      s_signed <= i_signed;
      s_num    <= i_numerator;
      s_den    <= i_denominator;
    end
  end

  // Reset state
  property p_reset_state;
    @(posedge i_clk)
      i_reset |=> (!o_busy && !o_valid && !o_err &&
                   !r_busy && !zero_divisor &&
                   r_bit=='0 && !last_bit && !pre_sign &&
                   !r_z && r_dividend=='0 &&
                   o_quotient=='0 && !r_c &&
                   r_divisor=='0);
  endproperty
  assert property (p_reset_state);

  // Handshake/protocol
  assert property (@(posedge i_clk) i_wr |=> o_busy);
  assert property (@(posedge i_clk) o_busy |-> !i_wr);
  assert property (@(posedge i_clk) !(o_busy && o_valid));
  assert property (@(posedge i_clk) o_err |-> o_valid);
  assert property (@(posedge i_clk) $fell(o_busy) |-> o_valid);
  assert property (@(posedge i_clk) o_valid |-> !o_busy);
  assert property (@(posedge i_clk) r_busy |-> o_busy);

  // Zero-divide behavior (1-cycle busy, valid+err set)
  assert property (@(posedge i_clk)
    i_wr && (i_denominator==0) |=> (!o_busy && o_valid && o_err));

  // Bounded completion for non-zero denominator
  localparam int ITER = (1<<LGBW);
  assert property (@(posedge i_clk)
    i_wr && (i_denominator!=0) |-> ##[1:ITER+1] (o_valid && !o_err));

  // Functional correctness at completion (uses captured operands)
  // Unsigned
  assert property (@(posedge i_clk)
    disable iff (i_reset)
    o_valid && !o_err && s_valid && !s_signed |-> o_quotient == (s_num / s_den));

  // Signed (2's complement, trunc toward zero)
  assert property (@(posedge i_clk)
    disable iff (i_reset)
    o_valid && !o_err && s_valid && s_signed |-> $signed(o_quotient) == ($signed(s_num) / $signed(s_den)));

  // Flags
  assert property (@(posedge i_clk) o_valid && !o_err |-> r_z == (o_quotient==0));
  assert property (@(posedge i_clk) o_valid |-> o_flags == {1'b0, o_quotient[BW-1], r_c, r_z});

  // Pre-sign is only set on a write with signed and any negative operand
  assert property (@(posedge i_clk)
    pre_sign |-> $past(i_wr) && $past(i_signed) &&
               ($past(i_numerator[BW-1]) || $past(i_denominator[BW-1])));

  // Micro-steps of restoring division when active
  // Divisor shift-right with zero fill MSB
  assert property (@(posedge i_clk)
    $past(r_busy && !pre_sign) |-> r_divisor == {1'b0, $past(r_divisor[2*BW-2:1])});

  // Quotient LSB set equals comparator result
  assert property (@(posedge i_clk)
    $past(r_busy && ($past(r_divisor[2*BW-2:BW])=='0)) |-> o_quotient[0] == !$past(diff[BW]));

  // Dividend update on successful subtract, otherwise hold
  assert property (@(posedge i_clk)
    $past(r_busy && ($past(r_divisor[2*BW-2:BW])=='0)) |->
      r_dividend == ($past(diff[BW]) ? $past(r_dividend) : $past(diff[BW-1:0])));

  // Coverage: basic scenarios
  cover property (@(posedge i_clk) i_wr && (i_denominator!=0) && !i_signed ##[1:ITER+1] o_valid && !o_err);
  cover property (@(posedge i_clk) i_wr && (i_denominator!=0) && i_signed && i_numerator[BW-1] && !i_denominator[BW-1] ##[1:ITER+1] o_valid && !o_err);
  cover property (@(posedge i_clk) i_wr && (i_denominator==0) ##1 o_valid && o_err);
  cover property (@(posedge i_clk) i_wr && (i_denominator!=0) && (i_numerator==0) ##[1:ITER+1] o_valid && !o_err && (o_quotient==0));

endmodule

// Bind example (instantiate once per DUT instance)
bind zipdiv zipdiv_sva #(.BW(BW), .LGBW(LGBW)) zipdiv_sva_i (
  .i_clk(i_clk), .i_reset(i_reset),
  .i_wr(i_wr), .i_signed(i_signed),
  .i_numerator(i_numerator), .i_denominator(i_denominator),
  .o_busy(o_busy), .o_valid(o_valid), .o_err(o_err),
  .o_quotient(o_quotient), .o_flags(o_flags),
  .r_busy(r_busy), .r_divisor(r_divisor), .r_dividend(r_dividend),
  .r_sign(r_sign), .pre_sign(pre_sign), .r_z(r_z), .r_c(r_c),
  .last_bit(last_bit), .r_bit(r_bit), .zero_divisor(zero_divisor)
);