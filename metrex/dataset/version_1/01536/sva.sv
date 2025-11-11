// SVA for d_ff
module d_ff_sva (
  input  logic        clock,
  input  logic        reset,
  input  logic [10:0] io_in,
  input  logic [10:0] io_init,
  input  logic [10:0] io_out,
  input  logic        io_enable,
  input  logic [10:0] d,
  input  logic [10:0] ff
);
  default clocking cb @(posedge clock); endclocking

  bit past_valid;
  always @(posedge clock) past_valid <= 1'b1;

  // Combinational path: d = (io_enable ? io_in : ff)
  assert property ( !$isunknown(io_enable) |-> (d == (io_enable ? io_in : ff)) );

  // Reset dominates: on cycle after reset high, output == prior io_init
  assert property ( past_valid && $past(reset) |-> (io_out == $past(io_init)) );

  // Load when enabled (no reset): on cycle after enable high, output == prior io_in
  assert property ( past_valid && !$past(reset) && $past(io_enable) |-> (io_out == $past(io_in)) );

  // Hold when disabled (no reset): on cycle after enable low, output holds prior value
  assert property ( past_valid && !$past(reset) && !$past(io_enable) |-> (io_out == $past(io_out)) );

  // Control signals should not be X/Z at sampling
  assert property ( !$isunknown({reset, io_enable}) );

  // Output becomes known after a controlling event (reset or load)
  assert property ( past_valid && ($past(reset) || $past(io_enable)) |-> !$isunknown(io_out) );

  // Coverage
  cover property ( past_valid && $past(reset) );
  cover property ( past_valid && !$past(reset) && $past(io_enable) && (io_out == $past(io_in)) );
  cover property ( past_valid && !$past(reset) && !$past(io_enable) && (io_out == $past(io_out)) );
  cover property ( past_valid && $past(io_enable) && (io_out != $past(io_out)) );
endmodule

// Bind into DUT
bind d_ff d_ff_sva sva_inst (
  .clock(clock),
  .reset(reset),
  .io_in(io_in),
  .io_init(io_init),
  .io_out(io_out),
  .io_enable(io_enable),
  .d(d),
  .ff(ff)
);