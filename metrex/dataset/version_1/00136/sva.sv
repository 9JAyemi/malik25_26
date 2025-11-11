// SVA checker for shifter_adder
module shifter_adder_sva (
  input         clk,
  input         reset,
  input         load,
  input  [1:0]  ena,
  input  [15:0] in,
  input         select,
  input  [15:0] q,
  input  [99:0] shift_reg,
  input  [15:0] adder_out,
  input  [15:0] shift_out
);

  default clocking cb @(posedge clk); endclocking

  // Basic mux consistency (combinational assign)
  assert property (q == (select ? adder_out : shift_out));

  // Synchronous reset clears all state by next cycle
  assert property ($past(reset) |-> (shift_reg == '0 && adder_out == '0 && shift_out == '0 && q == '0));

  // Load has priority over ena; zero-extend into shift_reg
  assert property (disable iff (reset)
    load |=> (shift_reg[15:0] == $past(in) && shift_reg[99:16] == '0));

  // Rotate-left when ena==00 and not loading
  assert property (disable iff (reset)
    (!load && ena == 2'b00) |=> shift_reg == { $past(shift_reg[98:0]), $past(shift_reg[99]) });

  // Rotate-right when ena==01 and not loading
  assert property (disable iff (reset)
    (!load && ena == 2'b01) |=> shift_reg == { $past(shift_reg[0]), $past(shift_reg[99:1]) });

  // Hold when ena is 10/11 and not loading
  assert property (disable iff (reset)
    (!load && (ena inside {2'b10,2'b11})) |=> shift_reg == $past(shift_reg));

  // Adder path updates only when select=1; 16-bit add by +16
  assert property (disable iff (reset)
    select |=> adder_out == ($past(in) + 16'h0010));

  // shift_out updates only when select=0 with upper 16 bits of shift_reg (from same cycle's pre-update value)
  assert property (disable iff (reset)
    !select |=> shift_out == $past(shift_reg[99:84]));

  // Hold the inactive datapath register
  assert property (disable iff (reset)
    select |=> shift_out == $past(shift_out));
  assert property (disable iff (reset)
    !select |=> adder_out == $past(adder_out));

  // Functional coverage
  cover property (disable iff (reset)
    load ##1 (!load && ena==2'b00) ##1 (!load && ena==2'b01) ##1 (ena inside {2'b10,2'b11}));

  // Cover wrap-around bits for both rotations
  cover property (disable iff (reset)
    (!load && ena==2'b00 && $past(shift_reg[99])) |=> shift_reg[0]);
  cover property (disable iff (reset)
    (!load && ena==2'b01 && $past(shift_reg[0]))  |=> shift_reg[99]);

  // Cover both datapaths exercised
  cover property (disable iff (reset) select ##1 !select);
  cover property (disable iff (reset) !select ##1 select);

endmodule

// Bind into DUT; internal regs are connected by name
bind shifter_adder shifter_adder_sva u_shifter_adder_sva (
  .clk       (clk),
  .reset     (reset),
  .load      (load),
  .ena       (ena),
  .in        (in),
  .select    (select),
  .q         (q),
  .shift_reg (shift_reg),
  .adder_out (adder_out),
  .shift_out (shift_out)
);