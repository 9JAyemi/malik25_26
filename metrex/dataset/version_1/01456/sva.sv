// SVA for sd2_dac
// Bindable, concise, checks key behaviors and provides focused coverage.

module sd2_dac_sva #(
  parameter int DW  = 16,
  parameter int CW  = 2,
  parameter int RW  = 4,
  parameter int A1W = 2,
  parameter int A2W = 5,
  parameter int ID  = 4
)(
  input  logic                 clk,

  // DUT ports
  input  logic [DW-1:0]        ldatasum,
  input  logic [DW-1:0]        rdatasum,
  input  logic                 left,
  input  logic                 right,

  // DUT internals (connect via bind)
  input  logic [DW+2-1:0]             ldata_gain,
  input  logic [DW+2-1:0]             rdata_gain,

  input  logic [DW-1:0]               ldata_cur,
  input  logic [DW-1:0]               ldata_prev,
  input  logic [DW-1:0]               rdata_cur,
  input  logic [DW-1:0]               rdata_prev,
  input  logic [DW+1-1:0]             ldata_step,
  input  logic [DW+1-1:0]             rdata_step,
  input  logic [DW+ID-1:0]            ldata_int,
  input  logic [DW+ID-1:0]            rdata_int,
  input  logic [DW-1:0]               ldata_int_out,
  input  logic [DW-1:0]               rdata_int_out,

  input  logic [DW+2+0-1:0]           sd_l_er0,
  input  logic [DW+2+0-1:0]           sd_r_er0,
  input  logic [DW+2+0-1:0]           sd_l_er0_prev,
  input  logic [DW+2+0-1:0]           sd_r_er0_prev,
  input  logic [DW+A1W+2-1:0]         sd_l_aca1,
  input  logic [DW+A1W+2-1:0]         sd_r_aca1,
  input  logic [DW+A2W+2-1:0]         sd_l_aca2,
  input  logic [DW+A2W+2-1:0]         sd_r_aca2,
  input  logic [DW+A1W+2-1:0]         sd_l_ac1,
  input  logic [DW+A1W+2-1:0]         sd_r_ac1,
  input  logic [DW+A2W+2-1:0]         sd_l_ac2,
  input  logic [DW+A2W+2-1:0]         sd_r_ac2,
  input  logic [DW+A2W+3-1:0]         sd_l_quant,
  input  logic [DW+A2W+3-1:0]         sd_r_quant,

  input  logic [24-1:0]               seed1,
  input  logic [19-1:0]               seed2,
  input  logic [24-1:0]               seed_sum,
  input  logic [24-1:0]               seed_prev,
  input  logic [24-1:0]               seed_out,

  input  logic [ID-1:0]               int_cnt
);

  default clocking cb @(posedge clk); endclocking

  // past-valid guard
  logic past_v; initial past_v = 1'b0; always @(cb) past_v <= 1'b1;

  // Basic X-prop checks
  assert property ( !$isunknown(left)  );
  assert property ( !$isunknown(right) );
  assert property ( !$isunknown(sd_l_er0[DW+2-1]) );
  assert property ( !$isunknown(sd_r_er0[DW+2-1]) );

  // LFSR seed1 behavior
  assert property ( disable iff (!past_v)
    $past(&seed1) |-> seed1 == 24'h654321
  );
  assert property ( disable iff (!past_v)
    !$past(&seed1) |-> seed1 ==
      { $past(seed1[22:0]),
        ~($past(seed1[23]) ^ $past(seed1[22]) ^ $past(seed1[21]) ^ $past(seed1[16])) }
  );

  // LFSR seed2 behavior
  assert property ( disable iff (!past_v)
    $past(&seed2) |-> seed2 == 19'h12345
  );
  assert property ( disable iff (!past_v)
    !$past(&seed2) |-> seed2 ==
      { $past(seed2[17:0]),
        ~($past(seed2[18]) ^ $past(seed2[17]) ^ $past(seed2[16]) ^ $past(seed2[13]) ^ $past(seed2[0])) }
  );

  // Dither sum/prev/out pipeline
  assert property ( seed_sum == (seed1 + {5'b0, seed2}) );
  assert property ( disable iff (!past_v) seed_prev == $past(seed_sum) );
  assert property ( disable iff (!past_v) seed_out  == seed_sum - $past(seed_sum) );

  // Integrator tick counter monotonic increment (wrap by width)
  assert property ( disable iff (!past_v) int_cnt == $past(int_cnt) + 'd1 );

  // Interpolator: sample/update behavior at frame start
  assert property ( disable iff (!past_v)
    $past(~|int_cnt) |-> (
      ldata_prev == $past(ldata_cur) &&
      rdata_prev == $past(rdata_cur) &&
      ldata_cur  == $past(ldatasum)  &&
      rdata_cur  == $past(rdatasum)  &&
      ldata_int  == { $past(ldata_cur[DW-1]), $past(ldata_cur), {ID{1'b0}} } &&
      rdata_int  == { $past(rdata_cur[DW-1]), $past(rdata_cur), {ID{1'b0}} }
    )
  );

  // Interpolator: accumulate intermediate steps
  assert property ( disable iff (!past_v)
    $past(|int_cnt) |-> (
      ldata_int == $past(ldata_int) + {{ID{$past(ldata_step[DW])}}, $past(ldata_step)} &&
      rdata_int == $past(rdata_int) + {{ID{$past(rdata_step[DW])}}, $past(rdata_step)}
    )
  );

  // Output of integrator bit-slice check
  assert property ( ldata_int_out == ldata_int[DW+ID-1:ID] );
  assert property ( rdata_int_out == rdata_int[DW+ID-1:ID] );

  // Gain: 3x with proper sign-extension
  assert property (
    ldata_gain == ({ldata_int_out[DW-1], ldata_int_out, 1'b0} + {{2{ldata_int_out[DW-1]}}, ldata_int_out})
  );
  assert property (
    rdata_gain == ({rdata_int_out[DW-1], rdata_int_out, 1'b0} + {{2{rdata_int_out[DW-1]}}, rdata_int_out})
  );

  // Pipeline registers capture combinational next values
  assert property ( disable iff (!past_v) sd_l_ac1 == $past(sd_l_aca1) );
  assert property ( disable iff (!past_v) sd_r_ac1 == $past(sd_r_aca1) );
  assert property ( disable iff (!past_v) sd_l_ac2 == $past(sd_l_aca2) );
  assert property ( disable iff (!past_v) sd_r_ac2 == $past(sd_r_aca2) );

  // Quantizer to 1-bit code mapping (rail codes only)
  localparam int QW = DW + A2W + 3;
  localparam int EW = DW + 2;
  assert property ( sd_l_quant[QW-1] |-> sd_l_er0 == {1'b1, {(EW-1){1'b0}}} );
  assert property ( !sd_l_quant[QW-1] |-> sd_l_er0 == {1'b0, {(EW-1){1'b1}}} );
  assert property ( sd_r_quant[QW-1] |-> sd_r_er0 == {1'b1, {(EW-1){1'b0}}} );
  assert property ( !sd_r_quant[QW-1] |-> sd_r_er0 == {1'b0, {(EW-1){1'b1}}} );

  // Previous error code update (+1 unless all-ones, which is unreachable here)
  assert property ( disable iff (!past_v)
    sd_l_er0_prev == ( $past(&sd_l_er0) ? $past(sd_l_er0) : ($past(sd_l_er0) + {{(EW-1){1'b0}},1'b1}) )
  );
  assert property ( disable iff (!past_v)
    sd_r_er0_prev == ( $past(&sd_r_er0) ? $past(sd_r_er0) : ($past(sd_r_er0) + {{(EW-1){1'b0}},1'b1}) )
  );

  // Output bit behavior
  assert property ( (~|ldata_gain) |-> left  == ~ $past(left) );
  assert property ( ( |ldata_gain) |-> left  == ~ sd_l_er0[EW-1] );
  assert property ( (~|rdata_gain) |-> right == ~ $past(right) );
  assert property ( ( |rdata_gain) |-> right == ~ sd_r_er0[EW-1] );

  // Sanity: sd_*_er0 only two legal patterns
  assert property ( sd_l_er0 == {1'b1, {(EW-1){1'b0}}} || sd_l_er0 == {1'b0, {(EW-1){1'b1}}} );
  assert property ( sd_r_er0 == {1'b1, {(EW-1){1'b0}}} || sd_r_er0 == {1'b0, {(EW-1){1'b1}}} );

  // Coverage

  // Seeds wrap/reload and non-zero dither
  cover property ( $rose(&seed1) ); // seed1 reload path can trigger
  cover property ( $rose(&seed2) ); // seed2 reload path can trigger
  cover property ( seed_out != '0 );

  // Counter wrap
  cover property ( past_v && ~|int_cnt && $past(int_cnt) == {ID{1'b1}} );

  // DAC outputs exercise both states and toggle on zero-gain
  cover property ( left == 1'b0 ##1 left == 1'b1 );
  cover property ( right == 1'b0 ##1 right == 1'b1 );
  cover property ( (~|ldata_gain) && left != $past(left) );
  cover property ( (~|rdata_gain) && right != $past(right) );

  // Quantizer rails hit both polarities
  cover property ( sd_l_quant[QW-1] );
  cover property ( !sd_l_quant[QW-1] );
  cover property ( sd_r_quant[QW-1] );
  cover property ( !sd_r_quant[QW-1] );

endmodule

// Example bind (connect all internals)
// Place in a bind file or your testbench top:
// bind sd2_dac sd2_dac_sva #(.DW(16), .RW(4), .A1W(2), .A2W(5), .ID(4)) sd2_dac_sva_i (
//   .clk(clk),
//   .ldatasum(ldatasum), .rdatasum(rdatasum),
//   .left(left), .right(right),
//   .ldata_gain(ldata_gain), .rdata_gain(rdata_gain),
//   .ldata_cur(ldata_cur), .ldata_prev(ldata_prev), .rdata_cur(rdata_cur), .rdata_prev(rdata_prev),
//   .ldata_step(ldata_step), .rdata_step(rdata_step),
//   .ldata_int(ldata_int), .rdata_int(rdata_int),
//   .ldata_int_out(ldata_int_out), .rdata_int_out(rdata_int_out),
//   .sd_l_er0(sd_l_er0), .sd_r_er0(sd_r_er0),
//   .sd_l_er0_prev(sd_l_er0_prev), .sd_r_er0_prev(sd_r_er0_prev),
//   .sd_l_aca1(sd_l_aca1), .sd_r_aca1(sd_r_aca1),
//   .sd_l_aca2(sd_l_aca2), .sd_r_aca2(sd_r_aca2),
//   .sd_l_ac1(sd_l_ac1), .sd_r_ac1(sd_r_ac1),
//   .sd_l_ac2(sd_l_ac2), .sd_r_ac2(sd_r_ac2),
//   .sd_l_quant(sd_l_quant), .sd_r_quant(sd_r_quant),
//   .seed1(seed1), .seed2(seed2), .seed_sum(seed_sum), .seed_prev(seed_prev), .seed_out(seed_out),
//   .int_cnt(int_cnt)
// );