// SVA for top_module and priority_encoder
// Bind these after compiling the DUT.

module top_module_sva (
  input  clk,
  input  reset,
  input  slowena,
  input  [2:0] sel,
  input  [3:0] data0,
  input  [3:0] data1,
  input  [3:0] data2,
  input  [3:0] data3,
  input  [3:0] data4,
  input  [3:0] data5,
  input  [3:0] threshold,
  input  [3:0] count,
  input        high_if_count_greater_than_threshold,
  input  [3:0] final_output
);
  default clocking cb @(posedge clk); endclocking

  function automatic [3:0] sel_mux_value (input [2:0] s);
    case (s)
      3'd0: sel_mux_value = data0;
      3'd1: sel_mux_value = data1;
      3'd2: sel_mux_value = data2;
      3'd3: sel_mux_value = data3;
      3'd4: sel_mux_value = data4;
      3'd5: sel_mux_value = data5;
      default: sel_mux_value = 4'b0001; // default path when sel is 6 or 7
    endcase
  endfunction

  // Counter reset, hold, and increment (with wrap) checks
  assert property (reset |=> (count == 4'h0));
  assert property (disable iff (reset) (!slowena) |=> (count == $past(count)));
  assert property (disable iff (reset) (slowena) |=> (($past(count) == 4'hF) ? (count == 4'h0) : (count == $past(count)+1)));

  // Comparator correctness
  assert property (1'b1 |-> (high_if_count_greater_than_threshold == (count >= threshold)));

  // Final output correctness (note scalar AND extension in RTL)
  // Expected mux value from sel, then AND with replicated scalar 0/1 as coded (zero-extend to 4'b0000/0001)
  wire [3:0] exp_mux  = sel_mux_value(sel);
  wire       exp_high = (count >= threshold);
  wire [3:0] exp_final = exp_high ? (exp_mux & 4'b0001) : 4'b0000;
  assert property (1'b1 |-> (final_output == exp_final));

  // Sanity: outputs not X/Z after reset deasserted
  assert property (disable iff (reset) !$isunknown({count, high_if_count_greater_than_threshold, final_output}));

  // Useful covers
  cover property (slowena && (count == 4'hF) ##1 (count == 4'h0));         // wrap
  cover property (!$past(high_if_count_greater_than_threshold) && high_if_count_greater_than_threshold); // threshold crossing
  cover property (high_if_count_greater_than_threshold && (sel == 3'd0));
  cover property (high_if_count_greater_than_threshold && (sel == 3'd1));
  cover property (high_if_count_greater_than_threshold && (sel == 3'd2));
  cover property (high_if_count_greater_than_threshold && (sel == 3'd3));
  cover property (high_if_count_greater_than_threshold && (sel == 3'd4));
  cover property (high_if_count_greater_than_threshold && (sel == 3'd5));
  cover property (high_if_count_greater_than_threshold && (sel >= 3'd6));   // default mux leg
  cover property (!high_if_count_greater_than_threshold && (sel == 3'd3));  // low comparator case through datapath
endmodule

bind top_module top_module_sva sva_top (.*);


// Direct checks for the combinational priority_encoder
module priority_encoder_sva (
  input  [2:0] in,
  input  [2:0] out
);
  // Truth-table check
  always @* begin
    assert ( (in <= 3'd5) ? (out == in) : (out == 3'd7) )
      else $error("priority_encoder mapping incorrect: in=%0b out=%0b", in, out);
    assert (!$isunknown(out))
      else $error("priority_encoder out is X/Z for in=%0b", in);
  end

  // Coverage of all meaningful input classes
  cover property (in == 3'd0);
  cover property (in == 3'd1);
  cover property (in == 3'd2);
  cover property (in == 3'd3);
  cover property (in == 3'd4);
  cover property (in == 3'd5);
  cover property ((in == 3'd6) && (out == 3'd7));
  cover property ((in == 3'd7) && (out == 3'd7));
endmodule

bind priority_encoder priority_encoder_sva sva_pe (.*);