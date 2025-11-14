// SVA for the provided DUT. Bind these into the design.

package top_module_sva_pkg;

  // 2:1 MUX checker (combinational)
  module mux_2to1_sva(input [3:0] in0, in1, input sel, input [3:0] out);
    // Functional correctness
    assert property (@(*) out == (sel ? in1 : in0)) else $error("MUX mismatch");
    // X/Z propagation check
    assert property (@(*) ($isunknown({sel,in0,in1})==0) |-> ($isunknown(out)==0)) else $error("MUX X/Z");
    // Coverage (both selections observed)
    cover property (@(*) (sel==0) && out==in0);
    cover property (@(*) (sel==1) && out==in1);
  endmodule

  // 4-bit shift register checker
  module shift_reg_4bit_sva(input [3:0] data_in, input shift, load, clk, reset, input [3:0] out);
    default clocking cb @(posedge clk); endclocking
    default disable iff (reset);

    // Async reset immediate effect
    assert property (@(posedge reset) out == 4'b0) else $error("SR async reset");

    // Priority and behaviors
    assert property (load |=> out == $past(data_in)) else $error("SR load");
    assert property (shift && load |=> out == $past(data_in)) else $error("SR load priority over shift");
    assert property (shift && !load |=> out == { $past(out[2:0]), 1'b0 }) else $error("SR shift-left-0");
    assert property (!load && !shift |=> out == $past(out)) else $error("SR hold");

    // X checks at active edge
    assert property (!$isunknown({load,shift,data_in})) else $error("SR X/Z on inputs");
    assert property (!reset |-> !$isunknown(out)) else $error("SR X/Z on output");

    // Coverage
    cover property (load);
    cover property (shift && !load);
    cover property (shift && load);
    cover property (load ##1 shift[*4]);
  endmodule

  // Top-level checker
  module top_module_sva(
    input clk, reset,
    input sel, input [3:0] data_in,
    input shift, load,
    input [3:0] shift_reg, input [3:0] mux_out,
    input [3:0] out
  );
    default clocking cb @(posedge clk); endclocking

    // Top output reset and 1-cycle tracking of shift_reg
    assert property (reset |-> out == 4'b0) else $error("TOP out not reset");
    assert property (!reset && $past(!reset) |-> out == $past(shift_reg)) else $error("TOP out not tracking shift_reg");

    // End-to-end datapath on load (through mux selection)
    assert property (!reset && load && (sel==1'b0) |=> shift_reg == $past(data_in)) else $error("E2E load from data_in");
    assert property (!reset && load && (sel==1'b1) |=> shift_reg == $past(shift_reg)) else $error("E2E self-load when sel=1");

    // Useful coverage
    cover property (reset ##1 !reset);
    cover property (!reset ##1 load ##1 shift);
  endmodule

endpackage

// Bind into DUT instances
bind mux_2to1       top_module_sva_pkg::mux_2to1_sva        i_mux_sva(.*);
bind shift_reg_4bit top_module_sva_pkg::shift_reg_4bit_sva  i_sr_sva(.*);
bind top_module     top_module_sva_pkg::top_module_sva       i_top_sva(.*);