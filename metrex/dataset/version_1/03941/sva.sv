// SVA for gray_counter and top_module (bind-ready). Focused, high-quality checks and coverage.

module gray_counter_sva (
  input logic        clk,
  input logic        reset,       // active-low
  input logic [3:0]  gray_count,
  input logic [3:0]  binary_count
);
  default clocking cb @(posedge clk); endclocking

  function automatic logic [3:0] bin2gray(input logic [3:0] b);
    return b ^ (b >> 1);
  endfunction

  // Reset holds count at 0
  a_rst_hold: assert property ( !reset |-> (binary_count == 4'h0) );

  // Increment by 1 modulo-16 when out of reset
  a_cnt_inc: assert property ( disable iff(!reset)
                               binary_count == (( $past(binary_count) + 4'h1 ) & 4'hF) );

  // Correct Gray mapping
  a_gray_map: assert property ( gray_count == bin2gray(binary_count) );

  // Successive Gray values differ by exactly 1 bit
  a_gray_step: assert property ( disable iff(!reset)
                                 $onehot( gray_count ^ $past(gray_count) ) );

  // No X/Z once out of reset
  a_no_x: assert property ( disable iff(!reset) !$isunknown({binary_count, gray_count}) );

  // Coverage
  // - Observe reset edges
  c_rst_assert:   cover property (@(negedge reset) 1);
  c_rst_deassert: cover property ( $rose(reset) );

  // - Wrap coverage: F -> 0
  c_wrap: cover property ( disable iff(!reset)
                           ($past(binary_count) == 4'hF) && (binary_count == 4'h0) );

  // - Hit all 16 count states
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : C_BIN_STATES
      c_bin_val: cover property ( disable iff(!reset) binary_count == logic'(i[3:0]) );
    end
  endgenerate
endmodule

bind gray_counter gray_counter_sva u_gray_counter_sva (
  .clk(clk),
  .reset(reset),
  .gray_count(gray_count),
  .binary_count(binary_count)
);


// Top-level SVA (covers concatenation and reset behavior, implicitly checks comb module)
module top_module_sva (
  input  logic        clk,
  input  logic        reset,     // active-low
  input  logic [7:0]  in_hi,
  input  logic [7:0]  in_lo,
  input  logic [19:0] out,
  input  logic [15:0] comb_out,
  input  logic [3:0]  gray_count
);
  default clocking cb @(posedge clk); endclocking

  // Async reset drives out to 0 at clock edges while held low
  a_top_rst_hold: assert property ( !reset |-> out == 20'h0 );

  // Output is concatenation of sub-block outputs when out of reset
  a_top_concat_full: assert property ( disable iff(!reset)
                                       out == {comb_out, gray_count} );

  // Directly check that the upper 16 bits reflect inputs (covers combinatorial_circuit)
  a_top_comb_passthru: assert property ( disable iff(!reset)
                                         out[19:4] == {in_hi, in_lo} );

  // Lower 4 bits mirror gray_count
  a_top_gray_passthru: assert property ( disable iff(!reset)
                                         out[3:0] == gray_count );

  // No X/Z once out of reset
  a_top_no_x: assert property ( disable iff(!reset) !$isunknown(out) );

  // Coverage: see a non-zero output and a change in out
  c_out_nonzero: cover property ( disable iff(!reset) out != 20'h0 );
  c_out_change:  cover property ( disable iff(!reset) out != $past(out) );
endmodule

bind top_module top_module_sva u_top_module_sva (
  .clk(clk),
  .reset(reset),
  .in_hi(in_hi),
  .in_lo(in_lo),
  .out(out),
  .comb_out(comb_out),
  .gray_count(gray_count)
);