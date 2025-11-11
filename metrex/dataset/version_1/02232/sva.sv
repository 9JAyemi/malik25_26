// SVA checker for mux6to1_pipeline
// Samples on a provided clock; bind this checker to the DUT from your TB.
module mux6to1_pipeline_sva #(parameter int W=4) (
  input  logic              clk,
  input  logic              rst_n,   // active-low; tie high if unused
  input  logic [2:0]        sel,
  input  logic [W-1:0]      data0,
  input  logic [W-1:0]      data1,
  input  logic [W-1:0]      data2,
  input  logic [W-1:0]      data3,
  input  logic [W-1:0]      data4,
  input  logic [W-1:0]      data5,
  input  logic [W-1:0]      out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Functional correctness for all select values, including default
  property p_mux_func;
    ((sel inside {3'b000}) |-> (out === data0)) &&
    ((sel inside {3'b001}) |-> (out === data1)) &&
    ((sel inside {3'b010}) |-> (out === data2)) &&
    ((sel inside {3'b011}) |-> (out === data3)) &&
    ((sel inside {3'b100}) |-> (out === data4)) &&
    ((sel inside {3'b101}) |-> (out === data5)) &&
    ((sel inside {3'b110,3'b111}) |-> (out === {W{1'bx}})) &&
    ($isunknown(sel)         |-> (out === {W{1'bx}}));
  endproperty
  a_mux_func: assert property (p_mux_func);

  // Optional sanity: when sel is valid and selected data is known, out is known (redundant, but explicit)
  a_no_x_when_valid_known: assert property (
    (sel inside {3'b000}) && !$isunknown(data0) |-> !$isunknown(out)
  );
  a_no_x_when_valid_known1: assert property (
    (sel inside {3'b001}) && !$isunknown(data1) |-> !$isunknown(out)
  );
  a_no_x_when_valid_known2: assert property (
    (sel inside {3'b010}) && !$isunknown(data2) |-> !$isunknown(out)
  );
  a_no_x_when_valid_known3: assert property (
    (sel inside {3'b011}) && !$isunknown(data3) |-> !$isunknown(out)
  );
  a_no_x_when_valid_known4: assert property (
    (sel inside {3'b100}) && !$isunknown(data4) |-> !$isunknown(out)
  );
  a_no_x_when_valid_known5: assert property (
    (sel inside {3'b101}) && !$isunknown(data5) |-> !$isunknown(out)
  );

  // Minimal functional coverage
  c_sel0: cover property ((sel == 3'b000) && (out === data0));
  c_sel1: cover property ((sel == 3'b001) && (out === data1));
  c_sel2: cover property ((sel == 3'b010) && (out === data2));
  c_sel3: cover property ((sel == 3'b011) && (out === data3));
  c_sel4: cover property ((sel == 3'b100) && (out === data4));
  c_sel5: cover property ((sel == 3'b101) && (out === data5));
  c_sel_invalid: cover property ((sel inside {3'b110,3'b111}) && (out === {W{1'bx}}));

endmodule

// Bind example (hook up clk/rst from your TB):
// bind mux6to1_pipeline mux6to1_pipeline_sva #(.W(4)) mux6to1_pipeline_sva_i (
//   .clk(tb_clk), .rst_n(tb_rst_n),
//   .sel(sel), .data0(data0), .data1(data1), .data2(data2),
//   .data3(data3), .data4(data4), .data5(data5), .out(out)
// );