// SVA checker for top_module
// Focus: reset behavior, mode selection, counter sequencing, mux mapping, output mapping, stability, and basic coverage.

module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic        select,
  input logic [3:0]  out,
  input logic [3:0]  counter1,
  input logic [3:0]  counter2,
  input logic [1:0]  select_counter,
  input logic [3:0]  mux_out
);

  // Useful function: DUT's out mapping when counters are selected
  function automatic logic [3:0] map_c1_to_out (input logic [3:0] c1);
    map_c1_to_out = (c1 <= 4'd8) ? c1 : (c1 - 4'd8);
  endfunction

  default clocking cb @(posedge clk); endclocking

  // ----------------------------------------
  // Reset checks (synchronous active-high)
  // ----------------------------------------
  // On a reset cycle, all internal regs specified in reset branch go to 0 next cycle
  a_reset_regs: assert property (@cb reset |=> (counter1==4'd0 && counter2==4'd0 &&
                                               select_counter==2'b00 && mux_out==4'd0));

  // After reset deasserted, select_counter only takes valid encodings (01 for counters, 10 for mux)
  a_selcnt_enum: assert property (@cb disable iff (reset) (1'b1 |-> (select_counter inside {2'b01,2'b10})));

  // ----------------------------------------
  // Mode = multiplexer (select=1)
  // ----------------------------------------
  // Next-cycle effects when select=1
  a_mux_mode: assert property (@cb disable iff (reset)
                               (select) |=> (select_counter==2'b10 &&
                                             mux_out==$past(counter2) &&
                                             counter1==$past(counter1) &&
                                             counter2==$past(counter2) &&
                                             out==$past(out))); // out is held in mux mode

  // ----------------------------------------
  // Mode = counters (select=0)
  // ----------------------------------------
  // Next-cycle effects when select=0: select_counter, out mapping, counter sequencing with wrap at 5
  a_cnt_mode: assert property (@cb disable iff (reset)
                               (!select) |=> (select_counter==2'b01 &&
                                              out==map_c1_to_out($past(counter1)) &&
                                              ( ($past(counter1)==4'd5)
                                                ? (counter1==4'd0 && counter2==$past(counter2)+1)
                                                : (counter1==$past(counter1)+1 && counter2==$past(counter2)) )));

  // mux_out is held when counters are selected
  a_mux_hold_in_cnt_mode: assert property (@cb disable iff (reset) (!select) |=> (mux_out==$past(mux_out)));

  // ----------------------------------------
  // Sanity/X checks (scoped to when signals are supposed to be meaningful)
  // ----------------------------------------
  a_no_x_cntregs: assert property (@cb disable iff (reset) !$isunknown({counter1,counter2,select_counter,mux_out}));
  a_no_x_out_when_driven: assert property (@cb disable iff (reset) (!select) |-> !$isunknown(out));

  // ----------------------------------------
  // Concise coverage
  // ----------------------------------------
  // Cover entering mux mode and holding it
  c_mux_hold: cover property (@cb disable iff (reset) select[*3]);

  // Cover switching between modes
  c_mode_toggle_10: cover property (@cb disable iff (reset) select ##1 !select);
  c_mode_toggle_01: cover property (@cb disable iff (reset) !select ##1 select);

  // Cover counter1 wrap at 5 and counter2 increment
  c_c1_wrap_inc_c2: cover property (@cb disable iff (reset)
                                    (!select && $past(!select) &&
                                     $past(counter1)==4'd5 && counter1==4'd0 &&
                                     counter2==$past(counter2)+1));

  // Cover counter2 wrap (via multiple wraps of counter1)
  c_c2_wrap: cover property (@cb disable iff (reset)
                             (!select && $past(!select) &&
                              $past(counter1)==4'd5 && $past(counter2)==4'hF &&
                              counter2==4'h0 && counter1==4'd0));

  // Cover key out mappings in counter mode
  c_out_0:  cover property (@cb disable iff (reset) (!select && $past(counter1)==4'd0 && out==4'd0));
  c_out_8:  cover property (@cb disable iff (reset) (!select && $past(counter1)==4'd8 && out==4'd8));
  c_out_9:  cover property (@cb disable iff (reset) (!select && $past(counter1)==4'd9 && out==4'd1));
  c_out_15: cover property (@cb disable iff (reset) (!select && $past(counter1)==4'd15 && out==4'd7));

  // Cover mux_out mirrors counter2 in mux mode
  c_mux_map_example: cover property (@cb disable iff (reset) (select && $past(counter2)==4'hA && mux_out==4'hA));

endmodule

// Bind into the DUT (connects to internal regs by name in the bound scope)
bind top_module top_module_sva i_top_module_sva (
  .clk(clk),
  .reset(reset),
  .select(select),
  .out(out),
  .counter1(counter1),
  .counter2(counter2),
  .select_counter(select_counter),
  .mux_out(mux_out)
);