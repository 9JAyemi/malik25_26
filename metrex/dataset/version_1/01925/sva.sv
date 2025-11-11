// SVA for pfpu_above
// Bind this file to the DUT. Focused, concise, and covers key behavior.

module pfpu_above_sva(
  input logic        sys_clk,
  input logic        alu_rst,
  input logic [31:0] a,
  input logic [31:0] b,
  input logic        valid_i,
  input logic [31:0] r,
  input logic        valid_o
);
  default clocking cb @(posedge sys_clk); endclocking

  localparam logic [31:0] ONE  = 32'h3f800000;
  localparam logic [31:0] ZERO = 32'h00000000;

  function automatic bit gt_from_bits (logic [31:0] aa, bb);
    bit sa = aa[31];
    bit sb = bb[31];
    if (!sa && !sb)      gt_from_bits = (aa[30:0] > bb[30:0]);
    else if (!sa && sb)  gt_from_bits = 1'b1;
    else if (sa && !sb)  gt_from_bits = 1'b0;
    else                 gt_from_bits = (aa[30:0] < bb[30:0]);
  endfunction

  // Output encoding and sanity
  assert property (r == ONE || r == ZERO) else $error("r must be 0.0 or 1.0");
  assert property (!$isunknown(r)) else $error("r is X/Z");
  assert property (!$isunknown(valid_o)) else $error("valid_o is X/Z");

  // Reset and valid pipeline behavior
  assert property (alu_rst |=> !valid_o) else $error("valid_o must clear on reset");
  assert property (disable iff (alu_rst || $past(alu_rst)) valid_o == $past(valid_i))
    else $error("valid_o must be 1-cycle delayed valid_i when not in/after reset");

  // Functional correctness: r reflects a>b (1-cycle latency)
  assert property (disable iff ($isunknown($past(a)) || $isunknown($past(b)))
                   ((r == ONE) == gt_from_bits($past(a), $past(b))))
    else $error("Functional mismatch: r != (a > b) per sign/magnitude spec");

  // Coverage
  cover property (r == ONE);
  cover property (r == ZERO);
  cover property ({a[31],b[31]} == 2'b00 ##1 (r == ONE));
  cover property ({a[31],b[31]} == 2'b00 ##1 (r == ZERO));
  cover property ({a[31],b[31]} == 2'b11 ##1 (r == ONE));
  cover property ({a[31],b[31]} == 2'b11 ##1 (r == ZERO));
  cover property ({a[31],b[31]} == 2'b01 ##1 (r == ONE));
  cover property ({a[31],b[31]} == 2'b10 ##1 (r == ZERO));
  cover property (alu_rst ##1 !valid_o);
  cover property (valid_i ##1 valid_o);

endmodule

bind pfpu_above pfpu_above_sva sva_i(
  .sys_clk(sys_clk),
  .alu_rst(alu_rst),
  .a(a),
  .b(b),
  .valid_i(valid_i),
  .r(r),
  .valid_o(valid_o)
);