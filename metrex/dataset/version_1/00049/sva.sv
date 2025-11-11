// SVA for priority_encoder
// Bindable checker module
module pe_sva (
  input logic [3:0] in,
  input logic [1:0] pos,
  input logic [3:0] in_inv,
  input logic [1:0] sel
);

  // Internal wiring correctness
  assert property (@(in)           ##0 in_inv == ~in)
    else $error("in_inv must be bitwise inversion of in");

  assert property (@(in or in_inv) ##0 sel    == in_inv[3:2])
    else $error("sel must mirror in_inv[3:2]");

  // Case mapping correctness
  assert property (@(sel)          ##0 pos    == sel)
    else $error("pos must mirror sel");

  // End-to-end functional equivalence
  assert property (@(in)           ##0 pos    == ~in[3:2])
    else $error("pos must equal ~in[3:2]");

  // Output independence from lower input bits
  assert property (@(in[1:0])      ##0 $stable(pos))
    else $error("pos must not change when in[1:0] changes");

  // X-propagation/knownness when inputs are known
  assert property (@(in) (!$isunknown(in[3:2])) |-> ##0 !$isunknown(pos))
    else $error("pos must be known when in[3:2] are known");

  // Coverage
  cover property (@(in)            ##0 pos == 2'b00);
  cover property (@(in)            ##0 pos == 2'b01);
  cover property (@(in)            ##0 pos == 2'b10);
  cover property (@(in)            ##0 pos == 2'b11);

  cover property (@(in[1:0])       ##0 $stable(pos));          // LSBs toggle with pos stable
  cover property (@(in[3:2])       ##0 $changed(pos));         // MSBs toggle with pos change

endmodule

// Bind into the DUT to observe internals
bind priority_encoder pe_sva pe_sva_i (
  .in(in),
  .pos(pos),
  .in_inv(in_inv),
  .sel(sel)
);