// SVA checker for top_module
module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [2:0]  sel,
  input  logic [3:0]  data0, data1, data2, data3, data4, data5,
  input  logic [3:0]  mux_out,
  input  logic [3:0]  nand_in,
  input  logic [3:0]  nand_in_neg,
  input  logic [3:0]  nand_out,
  input  logic [3:0]  out,
  input  logic        out_and,
  input  logic        out_or,
  input  logic        out_xor
);

  default clocking cb @(posedge clk); endclocking

  let valid_sel = (sel inside {3'b000,3'b001,3'b010,3'b011,3'b100,3'b101});
  let mo2 = $past(mux_out,2);

  // Async reset behavior (immediate and while asserted)
  assert property (@(posedge reset) (out==4'b0 && out_and==0 && out_or==0 && out_xor==0));
  assert property (@(posedge clk) reset |-> (out==4'b0 && out_and==0 && out_or==0 && out_xor==0));

  // Mux next-state mapping
  assert property (disable iff (reset) (sel==3'b000) |=> (mux_out==$past(data0)));
  assert property (disable iff (reset) (sel==3'b001) |=> (mux_out==$past(data1)));
  assert property (disable iff (reset) (sel==3'b010) |=> (mux_out==$past(data2)));
  assert property (disable iff (reset) (sel==3'b011) |=> (mux_out==$past(data3)));
  assert property (disable iff (reset) (sel==3'b100) |=> (mux_out==$past(data4)));
  assert property (disable iff (reset) (sel==3'b101) |=> (mux_out==$past(data5)));
  // Default (hold) on 110/111
  assert property (disable iff (reset) (sel inside {3'b110,3'b111}) |=> (mux_out==$past(mux_out)));

  // Pipeline correctness
  assert property (disable iff (reset) out == $past(mux_out));
  assert property (disable iff (reset) nand_in     == $past(mux_out));
  assert property (disable iff (reset) nand_in_neg == ~$past(mux_out));

  // NAND logic stage (from prior nand_in/nand_in_neg)
  assert property (disable iff (reset) nand_out[0] == $past(~&nand_in));
  assert property (disable iff (reset) nand_out[1] == $past(~&nand_in_neg));
  assert property (disable iff (reset) nand_out[2] == $past(~( nand_in[0] & nand_in_neg[1] & nand_in_neg[2] & nand_in[3]
                                                              | nand_in_neg[0] & nand_in[1] & nand_in[2] & nand_in_neg[3])));

  // Output stage (from prior nand_out)
  assert property (disable iff (reset) out_and == $past(nand_out[0]));
  assert property (disable iff (reset) out_or  == $past(nand_out[1]));
  assert property (disable iff (reset) out_xor == $past(nand_out[2]));

  // End-to-end functional equivalence (2-cycle latency from mux_out)
  assert property (disable iff (reset) out_and == ~&mo2);
  assert property (disable iff (reset) out_or  == |mo2);
  assert property (disable iff (reset) out_xor == ~( (mo2[0] & ~mo2[1] & ~mo2[2] & mo2[3])
                                                   | (~mo2[0] & mo2[1] & mo2[2] & ~mo2[3]) ));

  // Basic functional coverage
  cover property (@(posedge clk) !reset ##1 (sel==3'b000));
  cover property (@(posedge clk) !reset ##1 (sel==3'b001));
  cover property (@(posedge clk) !reset ##1 (sel==3'b010));
  cover property (@(posedge clk) !reset ##1 (sel==3'b011));
  cover property (@(posedge clk) !reset ##1 (sel==3'b100));
  cover property (@(posedge clk) !reset ##1 (sel==3'b101));
  cover property (@(posedge clk) !reset ##1 (sel inside {3'b110,3'b111}) ##1 (mux_out==$past(mux_out)));
  // Corner patterns for logical outputs (2-cycle latency observed)
  cover property (@(posedge clk) !reset ##2 (mo2==4'b0000) && (out_and==1) && (out_or==0));
  cover property (@(posedge clk) !reset ##2 (mo2==4'b1111) && (out_and==0) && (out_or==1));
  cover property (@(posedge clk) !reset ##2 (mo2==4'b1001) && (out_xor==0));
  cover property (@(posedge clk) !reset ##2 (mo2==4'b0110) && (out_xor==0));

endmodule

// Bind into DUT
bind top_module top_module_sva top_module_sva_i (
  .clk(clk),
  .reset(reset),
  .sel(sel),
  .data0(data0), .data1(data1), .data2(data2), .data3(data3), .data4(data4), .data5(data5),
  .mux_out(mux_out),
  .nand_in(nand_in),
  .nand_in_neg(nand_in_neg),
  .nand_out(nand_out),
  .out(out),
  .out_and(out_and),
  .out_or(out_or),
  .out_xor(out_xor)
);