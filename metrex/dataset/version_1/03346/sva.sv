// SVA for shift_register
// Bind module + assertions. Focused, concise, and covers all key behaviors.

module shift_register_sva (
  input  logic        CLK,
  input  logic        SHIFT,
  input  logic        LOAD,
  input  logic        mode,
  input  logic [15:0] DATA_IN,
  input  logic [15:0] DATA_OUT,
  input  logic [15:0] reg1,
  input  logic [15:0] reg2,
  input  logic [15:0] reg3,
  input  logic [15:0] reg4
);
  logic past_valid;
  always @(posedge CLK) past_valid <= 1'b1;

  default clocking cb @(posedge CLK); endclocking
  default disable iff (!past_valid);

  // Structural connectivity
  a_out_conn: assert property (DATA_OUT == reg4);

  // Hold when no operation
  a_hold: assert property ((!LOAD && !SHIFT) |-> {reg1,reg2,reg3,reg4} == $past({reg1,reg2,reg3,reg4}));

  // LOAD has priority over SHIFT; pipeline capture
  a_load: assert property (LOAD |-> (reg1 == $past(DATA_IN) &&
                                     reg2 == $past(reg1)    &&
                                     reg3 == $past(reg2)    &&
                                     reg4 == $past(reg3)));

  // SHIFT mode 0: right-shift with 0 fill, chained sources per RTL
  a_shift0: assert property (!LOAD && SHIFT && (mode==1'b0) |-> (
                              reg1 == {$past(reg2[14:0]),1'b0} &&
                              reg2 == {$past(reg3[14:0]),1'b0} &&
                              reg3 == {$past(reg4[14:0]),1'b0} &&
                              reg4 == {$past(reg4[14:0]),1'b0}));

  // SHIFT mode 1: right-shift with 1 fill
  a_shift1: assert property (!LOAD && SHIFT && (mode==1'b1) |-> (
                              reg1 == {$past(reg2[14:0]),1'b1} &&
                              reg2 == {$past(reg3[14:0]),1'b1} &&
                              reg3 == {$past(reg4[14:0]),1'b1} &&
                              reg4 == {$past(reg4[14:0]),1'b1}));

  // Simple functional coverage
  c_load:   cover property (LOAD);
  c_shift0: cover property (!LOAD && SHIFT && (mode==1'b0));
  c_shift1: cover property (!LOAD && SHIFT && (mode==1'b1));
  c_idle:   cover property (!LOAD && !SHIFT);
  c_both:   cover property (LOAD && SHIFT); // checks LOAD priority scenario
  c_mix:    cover property (LOAD ##1 (!LOAD && SHIFT)); // interaction sequence

endmodule

bind shift_register shift_register_sva svas (
  .CLK(CLK),
  .SHIFT(SHIFT),
  .LOAD(LOAD),
  .mode(mode),
  .DATA_IN(DATA_IN),
  .DATA_OUT(DATA_OUT),
  .reg1(reg1),
  .reg2(reg2),
  .reg3(reg3),
  .reg4(reg4)
);