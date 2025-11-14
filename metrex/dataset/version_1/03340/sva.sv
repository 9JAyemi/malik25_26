// SVA checker for pfpu_fmul
// Bind this checker to the DUT instance (bind shown at bottom)
module pfpu_fmul_sva (
  input logic         sys_clk,
  input logic         alu_rst,

  // DUT I/O
  input logic [31:0]  a,
  input logic [31:0]  b,
  input logic         valid_i,
  input logic [31:0]  r,
  input logic         valid_o,

  // DUT internals
  input logic         r_valid,
  input logic         r1_valid,
  input logic         r2_valid,

  input logic         r_zero,
  input logic         r1_zero,
  input logic         r2_zero,

  input logic         r_sign,
  input logic         r1_sign,
  input logic         r2_sign,

  input logic [7:0]   r_expn,
  input logic [7:0]   r1_expn,
  input logic [7:0]   r2_expn,

  input logic [23:0]  r_a_mant,
  input logic [23:0]  r_b_mant,
  input logic [47:0]  r1_mant,
  input logic [47:0]  r2_mant
);

  default clocking cb @(posedge sys_clk); endclocking
  default disable iff (alu_rst);

  // ---------------------------
  // Reset behavior
  // ---------------------------
  // Reset clears all valids immediately
  assert property (@(posedge sys_clk) alu_rst |-> (!r_valid && !r1_valid && !r2_valid && !valid_o));
  // No output valid if reset occurred in the last 3 cycles
  assert property (@(posedge sys_clk)
                   (alu_rst || $past(alu_rst,1) || $past(alu_rst,2) || $past(alu_rst,3)) |-> !valid_o);

  // ---------------------------
  // Valid pipeline
  // ---------------------------
  assert property (r_valid == valid_i);
  assert property (r1_valid == $past(r_valid,1,alu_rst));
  assert property (r2_valid == $past(r1_valid,1,alu_rst));
  assert property (valid_o == $past(r2_valid,1,alu_rst));
  // End-to-end valid latency = 3
  assert property (valid_o == $past(valid_i,3,alu_rst));

  // ---------------------------
  // Stage-0 decode/calc
  // ---------------------------
  assert property (r_zero == ((a[30:23]==8'd0) || (b[30:23]==8'd0)));
  assert property (r_sign == (a[31] ^ b[31]));
  assert property (r_expn == (a[30:23] + b[30:23] - 8'd127));
  assert property (r_a_mant == {1'b1, a[22:0]});
  assert property (r_b_mant == {1'b1, b[22:0]});

  // ---------------------------
  // Pipeline transfer
  // ---------------------------
  assert property (r1_zero == $past(r_zero,1,alu_rst));
  assert property (r2_zero == $past(r1_zero,1,alu_rst));

  assert property (r1_sign == $past(r_sign,1,alu_rst));
  assert property (r2_sign == $past(r1_sign,1,alu_rst));

  assert property (r1_expn == $past(r_expn,1,alu_rst));
  assert property (r2_expn == $past(r1_expn,1,alu_rst));

  assert property (r1_mant == ($past(r_a_mant,1,alu_rst) * $past(r_b_mant,1,alu_rst)));
  assert property (r2_mant == $past(r1_mant,1,alu_rst));

  // ---------------------------
  // Output assembly checks
  // ---------------------------
  // Zero-result path: exponent must be zero (sign/mant may be X by design)
  assert property (valid_o && r2_zero |-> (r[30:23] == 8'd0));

  // Normalization paths for non-zero
  assert property (valid_o && !r2_zero && !r2_mant[47] |-> r == {r2_sign,        r2_expn,        r2_mant[45:23]});
  assert property (valid_o && !r2_zero &&  r2_mant[47] |-> r == {r2_sign, (r2_expn+8'd1),        r2_mant[46:24]});

  // ---------------------------
  // End-to-end functional check (from inputs 3 cycles earlier)
  // ---------------------------
  // Matches architectural intent without relying on internals
  assert property (
    valid_o |-> (
      // zero case
      (($past(a,3,alu_rst)[30:23]==8'd0) || ($past(b,3,alu_rst)[30:23]==8'd0)) ?
        (r[30:23]==8'd0) :
      // non-zero cases
      (
        // compute product and fields from 3 cycles ago
        (
          !(({1'b1,$past(a,3,alu_rst)[22:0]} * {1'b1,$past(b,3,alu_rst)[22:0]})[47]) &&
          (r[31] == ($past(a,3,alu_rst)[31]^$past(b,3,alu_rst)[31])) &&
          (r[30:23] == ($past(a,3,alu_rst)[30:23] + $past(b,3,alu_rst)[30:23] - 8'd127)) &&
          (r[22:0]  == ({1'b1,$past(a,3,alu_rst)[22:0]} * {1'b1,$past(b,3,alu_rst)[22:0]})[45:23])
        )
        ||
        (
          ({1'b1,$past(a,3,alu_rst)[22:0]} * {1'b1,$past(b,3,alu_rst)[22:0]})[47] &&
          (r[31] == ($past(a,3,alu_rst)[31]^$past(b,3,alu_rst)[31])) &&
          (r[30:23] == (($past(a,3,alu_rst)[30:23] + $past(b,3,alu_rst)[30:23] - 8'd127) + 8'd1)) &&
          (r[22:0]  == ({1'b1,$past(a,3,alu_rst)[22:0]} * {1'b1,$past(b,3,alu_rst)[22:0]})[46:24])
        )
      )
    )
  );

  // ---------------------------
  // Minimal coverage
  // ---------------------------
  cover property (valid_i ##3 valid_o);                              // latency exercised
  cover property (valid_o && r2_zero);                                // zero path
  cover property (valid_o && !r2_zero && !r2_mant[47]);               // normalization no-shift
  cover property (valid_o && !r2_zero &&  r2_mant[47]);               // normalization with shift
  cover property (valid_o && r[31]);                                   // negative result
  cover property (valid_i ##1 valid_i ##3 valid_o ##1 valid_o);       // back-to-back
endmodule

// Bind example (place in a testbench or a package included by testbench)
bind pfpu_fmul pfpu_fmul_sva i_pfpu_fmul_sva (
  .sys_clk(sys_clk),
  .alu_rst(alu_rst),
  .a(a),
  .b(b),
  .valid_i(valid_i),
  .r(r),
  .valid_o(valid_o),

  .r_valid(r_valid),
  .r1_valid(r1_valid),
  .r2_valid(r2_valid),

  .r_zero(r_zero),
  .r1_zero(r1_zero),
  .r2_zero(r2_zero),

  .r_sign(r_sign),
  .r1_sign(r1_sign),
  .r2_sign(r2_sign),

  .r_expn(r_expn),
  .r1_expn(r1_expn),
  .r2_expn(r2_expn),

  .r_a_mant(r_a_mant),
  .r_b_mant(r_b_mant),
  .r1_mant(r1_mant),
  .r2_mant(r2_mant)
);