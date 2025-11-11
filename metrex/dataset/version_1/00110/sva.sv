// SVA for the provided design
// Focused, concise, module-bound checks with essential coverage.

////////////////////////////////////////////////////////////
// shift_reg assertions
////////////////////////////////////////////////////////////
module shift_reg_sva (
  input        clk,
  input [2:0]  select,
  input [7:0]  in,
  input [7:0]  out
);
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on select or out after first cycle
  assert property (past_valid |-> !$isunknown(select));
  assert property (past_valid |-> !$isunknown(out));

  // Functional next-state checks by select
  assert property (past_valid && select==3'b000 |-> out == $past(in));

  assert property (past_valid && select==3'b001 |-> 
                   (out[7]   == $past(in[7])    &&
                    out[6:0] == $past(out[6:0])));

  assert property (past_valid && select==3'b010 |-> 
                   (out[7:1] == $past(in[7:1])  &&
                    out[0]   == $past(out[0])));

  // Note: RHS concatenations in RTL are wider than 8; assignment truncates to LSBs.
  assert property (past_valid && select==3'b011 |-> 
                   out == { $past(in[0]),       $past(out[7:1]) });

  assert property (past_valid && select==3'b100 |-> 
                   out == { $past(in[1:0]),     $past(out[7:2]) });

  assert property (past_valid && select==3'b101 |-> 
                   out == { $past(in[2:0]),     $past(out[7:3]) });

  assert property (past_valid && select==3'b110 |-> 
                   out == { $past(in[3:0]),     $past(out[7:4]) });

  assert property (past_valid && select==3'b111 |-> 
                   out == { $past(in[4:0]),     $past(out[7:5]) });

  // Minimal functional coverage: see each select value
  cover property (past_valid && select==3'b000);
  cover property (past_valid && select==3'b001);
  cover property (past_valid && select==3'b010);
  cover property (past_valid && select==3'b011);
  cover property (past_valid && select==3'b100);
  cover property (past_valid && select==3'b101);
  cover property (past_valid && select==3'b110);
  cover property (past_valid && select==3'b111);
endmodule

bind shift_reg shift_reg_sva u_shift_reg_sva (.clk(clk), .select(select), .in(in), .out(out));

////////////////////////////////////////////////////////////
// reg_module assertions
////////////////////////////////////////////////////////////
module reg_module_sva (
  input        clk,
  input        reset,
  input [7:0]  in,
  input [7:0]  out
);
  default clocking cb @(posedge clk); endclocking

  // Async reset must take effect immediately at posedge reset
  assert property (@(posedge reset) out == 8'h00);

  // Synchronous behavior
  assert property (reset |-> out == 8'h00);
  assert property (!reset |-> out == $past(in));

  // Coverage: observe reset pulse and a normal capture
  cover property ($rose(reset));
  cover property (!reset ##1 !reset and out == $past(in));
endmodule

bind reg_module reg_module_sva u_reg_module_sva (.clk(clk), .reset(reset), .in(in), .out(out));

////////////////////////////////////////////////////////////
// concat_module assertions (combinational)
////////////////////////////////////////////////////////////
module concat_module_sva (
  input [7:0]   a, b, c, d,
  input [31:0]  out
);
  default clocking cb @(*); endclocking

  assert property (out == {a,b,c,d});

  // Minimal influence coverage: each byte drives its slice
  cover property ($changed(a) && $changed(out[31:24]));
  cover property ($changed(b) && $changed(out[23:16]));
  cover property ($changed(c) && $changed(out[15:8]));
  cover property ($changed(d) && $changed(out[7:0]));
endmodule

bind concat_module concat_module_sva u_concat_module_sva (.a(a), .b(b), .c(c), .d(d), .out(out));

////////////////////////////////////////////////////////////
// top_module end-to-end sanity and wiring checks
////////////////////////////////////////////////////////////
module top_module_sva (
  input         clk,
  input         reset,
  input [31:0]  in,
  input [31:0]  out
);
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Check fixed selects on instantiated shift_regs
  assert property (shift_reg1.select == 3'b001);
  assert property (shift_reg2.select == 3'b010);
  assert property (shift_reg3.select == 3'b111);

  // Wiring/concat sanity (combinational in hierarchy but sampled here)
  assert property (out == {shift_reg3.out, reg_module1.out, shift_reg2.out, in[7:0]});

  // Instance-level functional relations using top inputs
  // shift_reg1 (001): out MSB from in, lower bits shift
  assert property (past_valid |-> 
                   (shift_reg1.out[7]   == $past(in[23]) &&
                    shift_reg1.out[6:0] == $past(shift_reg1.out[6:0])));

  // reg_module follows shift_reg1 with 1-cycle latency, or holds 0 on reset
  assert property (reset |-> reg_module1.out == 8'h00);
  assert property (!reset |-> reg_module1.out == $past(shift_reg1.out));

  // shift_reg2 (010): upper 7 bits from in slice, LSB holds prior value
  assert property (past_valid |-> 
                   (shift_reg2.out[7:1] == $past(in[15:9]) &&
                    shift_reg2.out[0]   == $past(shift_reg2.out[0])));

  // shift_reg3 (111): top byte mixes in MSBs of in and prior upper bits
  assert property (past_valid |-> 
                   shift_reg3.out == { $past(in[31:27]), $past(shift_reg3.out[7:5]) });

  // End-to-end on top out[31:24] expressed only via top ports and past top out
  assert property (past_valid |-> 
                   out[31:24] == { $past(in[31:27]), $past(out[31:29]) });

  // Coverage: see a non-reset cycle and a reset pulse
  cover property ($rose(reset));
  cover property (past_valid && !reset);
endmodule

bind top_module top_module_sva u_top_module_sva (.clk(clk), .reset(reset), .in(in), .out(out));