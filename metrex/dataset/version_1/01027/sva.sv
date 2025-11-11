// SVA checker for multiply_by_3
module mul3_sva (
  input logic        clk,     // sampling clock (testbench-provided)
  input logic [3:0]  a,
  input logic [5:0]  out
);
  default clocking cb @(posedge clk); endclocking

  // No X/Z on interface
  assert property (!$isunknown(a));
  assert property (!$isunknown(out));

  // Functional correctness
  assert property (out == a*3);

  // Range (no overflow beyond 45)
  assert property (out inside {[6'd0:6'd45]});

  // Stability when input is stable
  assert property ($stable(a) |-> $stable(out));

  // Injectivity on observed samples: change in a implies change in out
  assert property (a != $past(a) |-> out != $past(out));

  // Coverage
  cover property ($changed(a) && out == a*3);
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cvr_all_inputs
      localparam int EXP = i*3;
      cover property (a == i[3:0] && out == EXP[5:0]);
    end
  endgenerate
endmodule

// Bind example (provide a free-running tb clock)
// bind multiply_by_3 mul3_sva u_mul3_sva(.clk(tb_clk), .a(a), .out(out));