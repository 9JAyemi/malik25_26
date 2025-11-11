// SVA package + bindable checkers for the given DUTs
package dut_sva_pkg;
  // 16-bit BCD increment helper (0000..9999 with ripple carry)
  function automatic logic [15:0] bcd_inc16(input logic [15:0] x);
    logic [3:0] d0,d1,d2,d3;
    d0 = x[3:0];  d1 = x[7:4];  d2 = x[11:8];  d3 = x[15:12];
    if (d0 == 4'd9) begin
      d0 = 4'd0;
      if (d1 == 4'd9) begin
        d1 = 4'd0;
        if (d2 == 4'd9) begin
          d2 = 4'd0;
          if (d3 == 4'd9) d3 = 4'd0;
          else            d3 = d3 + 4'd1;
        end else d2 = d2 + 4'd1;
      end else d1 = d1 + 4'd1;
    end else d0 = d0 + 4'd1;
    return {d3,d2,d1,d0};
  endfunction

  // 8-bit rotate-left by s (0..7)
  function automatic logic [7:0] rol8(input logic [7:0] x, input logic [2:0] s);
    if (s == 3'd0) return x;
    else           return (x << s) | (x >> (8 - s));
  endfunction

  function automatic bit bcd_nib_valid(input logic [3:0] d);
    return d <= 4'd9;
  endfunction
endpackage


// bcd_counter assertions
module bcd_counter_sva
  import dut_sva_pkg::*;
(
  input logic        clk,
  input logic        reset,
  input logic [3:1]  ena,
  input logic [15:0] q_bcd
);
  default clocking cb @(posedge clk); endclocking

  // Async reset immediate effect and hold
  assert property (@(posedge reset) q_bcd == 16'h0000);
  assert property (reset |-> q_bcd == 16'h0000);

  // Digits always valid BCD
  assert property (disable iff (reset)
    bcd_nib_valid(q_bcd[3:0]) &&
    bcd_nib_valid(q_bcd[7:4]) &&
    bcd_nib_valid(q_bcd[11:8]) &&
    bcd_nib_valid(q_bcd[15:12])
  );

  // Increment/hold behavior (ena[3] gates counting)
  assert property (disable iff (reset)
    ena[3] |-> q_bcd == bcd_inc16($past(q_bcd))
  );
  assert property (disable iff (reset)
    !ena[3] |-> q_bcd == $past(q_bcd)
  );

  // Key carry-chain coverage
  cover property (disable iff (reset)
    $past(ena[3]) && $past(q_bcd[3:0]) == 4'd9 &&
    q_bcd[3:0] == 4'd0 && q_bcd[7:4] == ($past(q_bcd[7:4]) + 4'd1)
  );
  cover property (disable iff (reset)
    $past(ena[3]) && $past(q_bcd[7:0]) == 8'h99 &&
    q_bcd[7:0] == 8'h00 && q_bcd[11:8] == ($past(q_bcd[11:8]) + 4'd1)
  );
  cover property (disable iff (reset)
    $past(ena[3]) && $past(q_bcd[11:0]) == 12'h999 &&
    q_bcd[11:0] == 12'h000 && q_bcd[15:12] == ($past(q_bcd[15:12]) + 4'd1)
  );
  cover property (disable iff (reset)
    $past(ena[3]) && $past(q_bcd) == 16'h9999 && q_bcd == 16'h0000
  );
endmodule


// parallel_load_shift assertions
module parallel_load_shift_sva
  import dut_sva_pkg::*;
(
  input logic       clk,
  input logic       reset,
  input logic [7:0] data_in,
  input logic [2:0] shift_amount,
  input logic [7:0] data_out
);
  default clocking cb @(posedge clk); endclocking

  // Async reset immediate effect and hold
  assert property (@(posedge reset) data_out == 8'h00);
  assert property (reset |-> data_out == 8'h00);

  // Rotate-left correctness sampled on clk
  assert property (disable iff (reset)
    data_out == rol8(data_in, shift_amount)
  );

  // Cover all shift amounts
  genvar i;
  generate
    for (i=0; i<8; i++) begin : g_cover_sa
      cover property (disable iff (reset) shift_amount == i[2:0]);
    end
  endgenerate
endmodule


// sum_module assertions (combinational)
module sum_module_sva
(
  input logic [15:0] bcd_in,
  input logic [7:0]  shift_in,
  input logic [7:0]  sum_out
);
  // Combinational equivalence
  assert property (sum_out == (bcd_in[15:8] + shift_in));

  // Cover overflow/wraparound
  cover property ((bcd_in[15:8] + shift_in) < bcd_in[15:8]);
endmodule


// top-level glue checks
module top_module_sva
(
  input logic       clk,
  input logic       reset,
  input logic [3:1] ena
);
  default clocking cb @(posedge clk); endclocking

  // Constant enable (width-safe)
  assert property (ena == 3'b111);
endmodule


// Bind into DUTs
bind bcd_counter        bcd_counter_sva        bcd_counter_sva_i(.*);
bind parallel_load_shift parallel_load_shift_sva pls_sva_i(.*);
bind sum_module         sum_module_sva         sum_module_sva_i(.*);
bind top_module         top_module_sva         top_module_sva_i(.*);