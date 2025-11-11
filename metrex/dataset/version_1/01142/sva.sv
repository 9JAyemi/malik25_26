// SVA for cordic_stage. Bind this file to the DUT.
module cordic_stage_sva #(parameter bitwidth=16, zwidth=16, shift=1)
(
  input logic                      clock,
  input logic                      reset,
  input logic                      enable,
  input logic [bitwidth-1:0]       xi, yi,
  input logic [zwidth-1:0]         zi, constant,
  input logic [bitwidth-1:0]       xo, yo,
  input logic [zwidth-1:0]         zo,
  input logic                      z_is_pos
);

  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // Parameter sanity
  initial assert (shift >= 1 && shift <= bitwidth-1);

  // Helper: arithmetic right shift implemented in DUT
  function automatic logic [bitwidth-1:0] arshift(input logic [bitwidth-1:0] v);
    arshift = {{shift+1{v[bitwidth-1]}}, v[bitwidth-2:shift]};
  endfunction

  // Basic structural checks
  assert property (z_is_pos == ~zi[zwidth-1]);
  assert property ((!reset && enable) |-> !$isunknown({xi, yi, zi, constant}));
  assert property (!$past(reset) |-> !$isunknown({xo, yo, zo}));

  // Reset behavior: drive and hold zeros while reset asserted
  assert property (reset |=> {xo,yo,zo} == '0);
  assert property ($past(reset) |-> {xo,yo,zo} == '0);

  // Functional update when enabled (one-cycle latency)
  assert property (
    $past(!reset && enable) |->
      ( xo == ( $past(zi[zwidth-1]) ? $past(xi) + arshift($past(yi))
                                     : $past(xi) - arshift($past(yi)) ) ) &&
      ( yo == ( $past(zi[zwidth-1]) ? $past(yi) - arshift($past(xi))
                                     : $past(yi) + arshift($past(xi)) ) ) &&
      ( zo == ( $past(zi[zwidth-1]) ? $past(zi) + $past(constant)
                                     : $past(zi) - $past(constant) ) )
  );

  // Hold behavior when disabled (expected; flags that DUT currently ignores enable)
  assert property ( $past(!reset) && !$past(enable) |-> {xo,yo,zo} == $past({xo,yo,zo}) );

  // Check that concatenation-based shift matches arithmetic shift semantics
  assert property ( $past(!reset && enable) |-> arshift($past(xi)) == $signed($past(xi)) >>> shift );
  assert property ( $past(!reset && enable) |-> arshift($past(yi)) == $signed($past(yi)) >>> shift );

  // Minimal functional coverage
  cover property ( $past(!reset && enable) && ($past(zi[zwidth-1]) == 1'b0) ); // z_is_pos branch
  cover property ( $past(!reset && enable) && ($past(zi[zwidth-1]) == 1'b1) ); // !z_is_pos branch
  cover property ( $rose(reset) );
  cover property ( $past(!reset) && !$past(enable) && {xo,yo,zo} == $past({xo,yo,zo}) );

endmodule

bind cordic_stage cordic_stage_sva #(.bitwidth(bitwidth), .zwidth(zwidth), .shift(shift)) cordic_stage_sva_i
(
  .clock(clock),
  .reset(reset),
  .enable(enable),
  .xi(xi),
  .yi(yi),
  .zi(zi),
  .constant(constant),
  .xo(xo),
  .yo(yo),
  .zo(zo),
  .z_is_pos(z_is_pos)
);