// SVA for separate_16_to_8
module separate_16_to_8_sva (
  input  logic [15:0] in,
  input  logic [7:0]  out_hi,
  input  logic [7:0]  out_lo
);

  // Core functional checks
  // out_hi always equals upper byte
  assert property (@(in) out_hi === in[15:8]);

  // out_lo behavior
  assert property (@(in) (in[7:0] === 8'h00) |-> (out_lo === 8'h00));
  assert property (@(in) (! $isunknown(in[7:0]) && (in[7:0] != 8'h00)) |-> (out_lo === in[15:8]));

  // Out_lo must be either 0 or upper when inputs known
  assert property (@(in) (! $isunknown(in[15:8]) && ! $isunknown(in[7:0]))
                   |-> ((out_lo === 8'h00) || (out_lo === in[15:8])));

  // Independence: out_hi does not depend on low byte
  assert property (@(in) ($changed(in[7:0]) && $stable(in[15:8])) |-> $stable(out_hi));

  // Basic X-prop sanity for out_hi
  assert property (@(in) (out_hi === in[15:8]));

  // Coverage
  cover property (@(in) in == 16'h0000);                                     // both zero
  cover property (@(in) (in[15:8] == 8'h00) && (in[7:0] != 8'h00) &&
                          ! $isunknown(in)) ;                                 // upper=0, lower!=0
  cover property (@(in) (in[15:8] != 8'h00) && (in[7:0] == 8'h00) &&
                          ! $isunknown(in)) ;                                 // upper!=0, lower=0
  cover property (@(in) (in[15:8] != 8'h00) && (in[7:0] != 8'h00) &&
                          ! $isunknown(in));                                   // both non-zero
  cover property (@(in) (! $isunknown(in[7:0]) && (in[7:0] != 8'h00) &&
                         (out_lo == in[15:8])));                               // lo->upper path
  cover property (@(in) (in[7:0] == 8'h00) && (out_lo == 8'h00));             // lo->zero path
endmodule

// Bind into DUT
bind separate_16_to_8 separate_16_to_8_sva i_separate_16_to_8_sva (
  .in(in),
  .out_hi(out_hi),
  .out_lo(out_lo)
);