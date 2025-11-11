// SVA for NormaliseProdMultDescale
// Concise checks of pass-throughs, active normalization branches, and branch coverage.

module NormaliseProdMultDescale_sva
(
  input  logic        clock,
  input  logic [32:0] zout_Multiply,
  input  logic [49:0] productout_Multiply,
  input  logic [7:0]  InsTagMultiply,
  input  logic        ScaleValidMultiply,
  input  logic [31:0] z_Multiply,
  input  logic        idle_Multiply,

  input  logic [32:0] zout_NormaliseProd,
  input  logic [49:0] productout_NormaliseProd,
  input  logic [7:0]  InsTagNormaliseProd,
  input  logic        ScaleValidNormaliseProd,
  input  logic [31:0] z_NormaliseProd
);

  // Parameter defaults mirror DUT
  parameter logic no_idle = 1'b0;
  parameter logic put_idle = 1'b1;

  logic past_valid;
  always_ff @(posedge clock) past_valid <= 1'b1;

  default clocking cb @(posedge clock); endclocking
  default disable iff (!past_valid);

  // Unconditional pass-throughs (registered one cycle later)
  assert property (1'b1 |=> z_NormaliseProd == $past(z_Multiply));
  assert property (1'b1 |=> ScaleValidNormaliseProd == $past(ScaleValidMultiply));
  assert property (1'b1 |=> InsTagNormaliseProd == $past(InsTagMultiply));
  assert property (1'b1 |=> idle_NormaliseProd == $past(idle_Multiply));

  // Idle path: full zout pass-through, productout holds its previous value
  assert property (idle_Multiply == put_idle |=> zout_NormaliseProd == $past(zout_Multiply));
  assert property (idle_Multiply == put_idle |=> productout_NormaliseProd == $past(productout_NormaliseProd));

  // Active path: disallow X on branch selector bit for robustness
  assert property (idle_Multiply == no_idle |-> !$isunknown(productout_Multiply[49]));

  // Active path: branch 1 (denorm exponent: exp < -126)
  assert property (
    idle_Multiply == no_idle && $signed(zout_Multiply[31:24]) < -126
    |=> (zout_NormaliseProd[32]    == $past(zout_Multiply[32]))
     && (zout_NormaliseProd[31:24] == $past(zout_Multiply[31:24]) + 1)
     && (zout_NormaliseProd[23:0]  == $past(zout_Multiply[23:0]))
     && (productout_NormaliseProd  == ($past(productout_Multiply) >> 1))
  );

  // Active path: branch 2 (MSB=0, shift left, exp - 1)
  assert property (
    idle_Multiply == no_idle
    && !($signed(zout_Multiply[31:24]) < -126)
    && productout_Multiply[49] == 1'b0
    |=> (zout_NormaliseProd[32]    == $past(zout_Multiply[32]))
     && (zout_NormaliseProd[31:24] == $past(zout_Multiply[31:24]) - 1)
     && (zout_NormaliseProd[23:0]  == $past(productout_Multiply[48:25]))
     && (productout_NormaliseProd  == ($past(productout_Multiply) << 1))
  );

  // Active path: branch 3 (MSB=1, keep exp, pass product, take [49:26])
  assert property (
    idle_Multiply == no_idle
    && !($signed(zout_Multiply[31:24]) < -126)
    && productout_Multiply[49] == 1'b1
    |=> (zout_NormaliseProd[32]    == $past(zout_Multiply[32]))
     && (zout_NormaliseProd[31:24] == $past(zout_Multiply[31:24]))
     && (zout_NormaliseProd[23:0]  == $past(productout_Multiply[49:26]))
     && (productout_NormaliseProd  == $past(productout_Multiply))
  );

  // Coverage: hit idle and all active branches, plus boundary cases around -126
  cover property (idle_Multiply == put_idle);

  cover property (idle_Multiply == no_idle && $signed(zout_Multiply[31:24]) < -126);
  cover property (idle_Multiply == no_idle && $signed(zout_Multiply[31:24]) == -126 && productout_Multiply[49] == 1'b0);
  cover property (idle_Multiply == no_idle && $signed(zout_Multiply[31:24]) == -126 && productout_Multiply[49] == 1'b1);
  cover property (idle_Multiply == no_idle && $signed(zout_Multiply[31:24]) > -126 && productout_Multiply[49] == 1'b0);
  cover property (idle_Multiply == no_idle && $signed(zout_Multiply[31:24]) > -126 && productout_Multiply[49] == 1'b1);

endmodule

// Bind into the DUT
bind NormaliseProdMultDescale NormaliseProdMultDescale_sva
#(.no_idle(no_idle), .put_idle(put_idle)) NormaliseProdMultDescale_sva_i
(
  .clock(clock),
  .zout_Multiply(zout_Multiply),
  .productout_Multiply(productout_Multiply),
  .InsTagMultiply(InsTagMultiply),
  .ScaleValidMultiply(ScaleValidMultiply),
  .z_Multiply(z_Multiply),
  .idle_Multiply(idle_Multiply),
  .zout_NormaliseProd(zout_NormaliseProd),
  .productout_NormaliseProd(productout_NormaliseProd),
  .InsTagNormaliseProd(InsTagNormaliseProd),
  .ScaleValidNormaliseProd(ScaleValidNormaliseProd),
  .z_NormaliseProd(z_NormaliseProd)
);