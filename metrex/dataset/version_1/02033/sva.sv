// SVA for binary_counter
// Bind this module to the DUT: bind binary_counter binary_counter_sva sva_inst (.*);

module binary_counter_sva (
  input clk,
  input reset,
  input count_en,
  input [31:0] max_count,
  input [31:0] load_val,
  input load,
  input count_dir,
  input [31:0] count_out
);

  // Asynchronous reset behavior
  ap_async_reset_edge: assert property (@(posedge reset) count_out == 32'b0);
  ap_reset_hold:       assert property (@(posedge clk) reset |-> count_out == 32'b0);

  // Load has priority, synchronous to clk
  ap_load_update: assert property (@(posedge clk) disable iff (reset)
                                   load |=> count_out == $past(load_val));

  // Idle hold (no load, no count)
  ap_idle_hold: assert property (@(posedge clk) disable iff (reset)
                                 (!load && !count_en) |=> $stable(count_out));

  // Up-count path
  ap_up_inc:  assert property (@(posedge clk) disable iff (reset)
                               (!load && count_en && count_dir && (count_out != max_count))
                               |=> count_out == $past(count_out) + 1);
  ap_up_wrap: assert property (@(posedge clk) disable iff (reset)
                               (!load && count_en && count_dir && (count_out == max_count))
                               |=> count_out == 32'b0);

  // Down-count path
  ap_dn_dec:  assert property (@(posedge clk) disable iff (reset)
                               (!load && count_en && !count_dir && (count_out != 32'b0))
                               |=> count_out == $past(count_out) - 1);
  ap_dn_wrap: assert property (@(posedge clk) disable iff (reset)
                               (!load && count_en && !count_dir && (count_out == 32'b0))
                               |=> count_out == max_count);

  // No spurious changes: any change must be due to load or legal count step
  ap_coherent_change: assert property (@(posedge clk) disable iff (reset)
    (!$stable(count_out)) |->
      ( load
        || ( count_en &&
             ( ( count_dir &&
                 ( ($past(count_out) == max_count) ? (count_out == 32'b0)
                                                   : (count_out == $past(count_out) + 1) ) )
               || (!count_dir &&
                 ( ($past(count_out) == 32'b0) ? (count_out == max_count)
                                               : (count_out == $past(count_out) - 1) ) ) ) ) ));

  // Output should not be X/Z after clock edges
  ap_no_x_out: assert property (@(posedge clk) !$isunknown(count_out));

  // ------------- Coverage -------------
  cv_reset_edge:   cover property (@(posedge reset) 1);
  cv_load:         cover property (@(posedge clk) disable iff (reset) load);
  cv_up_inc:       cover property (@(posedge clk) disable iff (reset)
                                   (!load && count_en && count_dir && (count_out != max_count))
                                   ##1 (count_out == $past(count_out) + 1));
  cv_up_wrap:      cover property (@(posedge clk) disable iff (reset)
                                   (!load && count_en && count_dir && (count_out == max_count))
                                   ##1 (count_out == 32'b0));
  cv_dn_dec:       cover property (@(posedge clk) disable iff (reset)
                                   (!load && count_en && !count_dir && (count_out != 32'b0))
                                   ##1 (count_out == $past(count_out) - 1));
  cv_dn_wrap:      cover property (@(posedge clk) disable iff (reset)
                                   (!load && count_en && !count_dir && (count_out == 32'b0))
                                   ##1 (count_out == max_count));
  cv_load_while_en: cover property (@(posedge clk) disable iff (reset)
                                    (count_en && load) ##1 (count_out == $past(load_val)));
  cv_dir_toggle_while_counting: cover property (@(posedge clk) disable iff (reset)
                                    (!load && count_en && count_dir) ##1 (!load && count_en && !count_dir));
  cv_maxcnt_zero_up: cover property (@(posedge clk) disable iff (reset)
                                    (max_count == 0 && !load && count_en && count_dir));

endmodule