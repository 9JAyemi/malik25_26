// SystemVerilog Assertions for johnson_counter, half_word_comb, top_module
// Bind into DUTs; focuses on correctness, reset behavior, state transitions, and data mapping.

///////////////////////////////////////////////////////////////////////////
// johnson_counter SVA
///////////////////////////////////////////////////////////////////////////
module johnson_counter_sva (input logic clk, input logic reset, input logic [3:0] out);
  default clocking cb @(posedge clk); endclocking

  // State must always be one of the 6 legal codes
  a_state_legal: assert property (state inside {3'b000,3'b100,3'b110,3'b111,3'b011,3'b001});

  // Synchronous active-high reset drives state to 000
  a_reset_state: assert property (reset |-> state == 3'b000);

  // Next-state mapping (from case statement), including recovery to 000 from illegal
  a_state_next: assert property (
    $past(1'b1) && !$past(reset) |->
      ( ($past(state)==3'b000 && state==3'b100)
      ||($past(state)==3'b100 && state==3'b110)
      ||($past(state)==3'b110 && state==3'b111)
      ||($past(state)==3'b111 && state==3'b011)
      ||($past(state)==3'b011 && state==3'b001)
      ||($past(state)==3'b001 && state==3'b000)
      ||(!($past(state) inside {3'b000,3'b100,3'b110,3'b111,3'b011,3'b001}) && state==3'b000) )
  );

  // out update uses previous state and previous out[3]
  a_out_next: assert property (
    $past(1'b1) |-> out == { $past(state[2]), $past(state[1]), $past(state[0]), $past(out[3]) }
  );

  // Functional coverage: complete 6-step Johnson sequence
  sequence jc_cycle;
    state==3'b000 ##1 state==3'b100 ##1 state==3'b110 ##1 state==3'b111 ##1 state==3'b011 ##1 state==3'b001 ##1 state==3'b000;
  endsequence
  c_full_cycle: cover property (disable iff (reset) jc_cycle);
endmodule

bind johnson_counter johnson_counter_sva jcsva (.*);

///////////////////////////////////////////////////////////////////////////
// half_word_comb SVA
///////////////////////////////////////////////////////////////////////////
module half_word_comb_sva (input logic [7:0] in_hi, input logic [7:0] in_lo, input logic [15:0] out);
  // Pure combinational mapping check
  always @* a_concat_map: assert (out === {in_hi, in_lo});
endmodule

bind half_word_comb half_word_comb_sva hwc_sva (.*);

///////////////////////////////////////////////////////////////////////////
// top_module SVA
///////////////////////////////////////////////////////////////////////////
module top_module_sva (input logic clk, input logic reset, input logic [79:0] out);
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset edge forces out to zero
  a_out_reset_async: assert property (@(posedge reset) out == 80'b0);

  // While reset is asserted at clk edge, out must be zero
  a_out_reset_sync: assert property (reset |-> out == 80'b0);

  // On non-reset clk edge: width/zero-extension and mapping with 1-cycle delay for johnson_out
  a_out_map: assert property (
    $past(1'b1) && !reset |->
      ( out[79:20] == 60'b0
        && out[19:4] == $past(half_word_out)
        && out[3:0]  == $past(johnson_out) )
  );

  // Coverage: observe a nonzero payload with proper zero-extension
  c_payload: cover property (!reset && out[79:20]==60'b0 && out[19:0] != 20'b0);
endmodule

bind top_module top_module_sva tmsva (.*);