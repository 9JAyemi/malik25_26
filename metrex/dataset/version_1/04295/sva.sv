// Bindable SVA for byte_swap
module byte_swap_sva;

  // Expected transforms
  logic [31:0] exp_shift, exp_out;

  // Immediate combinational checks
  always @* begin
    exp_shift = {in[7:0], in[15:8], in[23:16], in[31:24]};
    exp_out   = {~in[7:0], ~in[15:8], ~in[23:16], ~in[31:24]};

    // Internal stage checks
    assert (shift_reg === exp_shift)
      else $error("byte_swap: shift_reg mismatch. in=%h shift_reg=%h exp=%h", in, shift_reg, exp_shift);

    assert (byte0 === (shift_reg[7:0]   ^ 8'hFF))  else $error("byte0 mismatch");
    assert (byte1 === (shift_reg[15:8]  ^ 8'hFF))  else $error("byte1 mismatch");
    assert (byte2 === (shift_reg[23:16] ^ 8'hFF))  else $error("byte2 mismatch");
    assert (byte3 === (shift_reg[31:24] ^ 8'hFF))  else $error("byte3 mismatch");

    // Output functional check
    assert (out === exp_out)
      else $error("byte_swap: functional mismatch. in=%h out=%h exp=%h", in, out, exp_out);

    // X/Z propagation sanity
    if ($isunknown(in))  assert ($isunknown(out))  else $error("byte_swap: X on in should yield X on out");
    if (!$isunknown(in)) assert (!$isunknown(out)) else $error("byte_swap: clean in should yield clean out");
    if ($isunknown(in[31:24])) assert ($isunknown(out[7:0]))   else $error("X-prop MSB->LSB byte fail");
    if ($isunknown(in[23:16])) assert ($isunknown(out[15:8]))  else $error("X-prop byte2 fail");
    if ($isunknown(in[15:8]))  assert ($isunknown(out[23:16])) else $error("X-prop byte1 fail");
    if ($isunknown(in[7:0]))   assert ($isunknown(out[31:24])) else $error("X-prop LSB->MSB byte fail");
  end

  // Lightweight concurrent checks/coverage with event-based sampling
  event ev;
  always @(in or out) -> ev;
  default clocking cb @(ev); endclocking

  // Byte-isolation: each input byte only affects its mapped output byte
  property p_iso0; $changed(in[7:0])   && $stable(in[31:8])  |-> $changed(out[31:24]) && $stable(out[23:0]); endproperty
  property p_iso1; $changed(in[15:8])  && $stable(in[31:16]|in[7:0]) |-> $changed(out[23:16]) && $stable(out[31:24]|out[15:0]); endproperty
  property p_iso2; $changed(in[23:16]) && $stable(in[31:24]|in[15:0]) |-> $changed(out[15:8]) && $stable(out[31:16]|out[7:0]); endproperty
  property p_iso3; $changed(in[31:24]) && $stable(in[23:0])  |-> $changed(out[7:0])   && $stable(out[31:8]); endproperty
  assert property(p_iso0);
  assert property(p_iso1);
  assert property(p_iso2);
  assert property(p_iso3);

  // Functional equivalence (concurrent form)
  assert property (out == {~in[7:0], ~in[15:8], ~in[23:16], ~in[31:24]});

  // Corner-case coverage
  cover property (in == 32'h00000000 && out == 32'hFFFFFFFF);
  cover property (in == 32'hFFFFFFFF && out == 32'h00000000);
  cover property (in == 32'hA5A5A5A5 && out == 32'h5A5A5A5A);
  cover property (in == 32'h01234567 && out == 32'h98BADCFE);
  cover property (in == 32'h89ABCDEF && out == 32'h10325476);

  // Stimulus-style coverage: independent byte changes observed
  cover property ($changed(in[7:0])   && $stable(in[31:8]));
  cover property ($changed(in[15:8])  && $stable(in[31:16]|in[7:0]));
  cover property ($changed(in[23:16]) && $stable(in[31:24]|in[15:0]));
  cover property ($changed(in[31:24]) && $stable(in[23:0]));
  cover property ($changed(in)); // all bytes toggle activity

endmodule

// Bind into the DUT
bind byte_swap byte_swap_sva bs_sva();