// SVA checker for FxP_ABS_Function
// Bind or instantiate this module; connect any convenient free-running clk and an active-high rst_n.
module FxP_ABS_Function_sva #(
  parameter int DATA_WIDTH = 16
) (
  input  logic                         clk,
  input  logic                         rst_n,
  input  logic [DATA_WIDTH-1:0]        DATA_IN,
  input  logic [DATA_WIDTH-1:0]        DATA_ABS
);
  localparam int  DW = DATA_WIDTH;
  localparam logic [DW-1:0] MINNEG = (1'b1 << (DW-1));
  localparam logic [DW-1:0] MAXPOS = {1'b0, {DW-1{1'b1}}};
  localparam logic [DW-1:0] NEG1   = {DW{1'b1}};

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Functional equivalence to the spec
  assert property (DATA_ABS == (DATA_IN[DW-1] ? (~DATA_IN + 1'b1) : DATA_IN))
    else $error("ABS functional mismatch");

  // Output is non-negative except for the unrepresentable min-negative case
  assert property ((DATA_IN != MINNEG) |-> (DATA_ABS[DW-1] == 1'b0))
    else $error("ABS produced negative result for representable input");

  // Min-negative saturates to itself in 2's-complement arithmetic
  assert property ((DATA_IN == MINNEG) |-> (DATA_ABS == MINNEG))
    else $error("ABS min-negative handling incorrect");

  // Clean inputs yield clean outputs (no X/Z propagation)
  assert property ((!$isunknown(DATA_IN)) |-> (!$isunknown(DATA_ABS)))
    else $error("ABS produced X/Z on clean input");

  // Coverage: exercise key input classes and boundaries
  cover property (DATA_IN == '0);                    // zero
  cover property (!DATA_IN[DW-1] && (DATA_IN != '0)); // positive
  cover property (DATA_IN[DW-1] && (DATA_IN != MINNEG)); // negative (not minneg)
  cover property (DATA_IN == MINNEG);                // min-negative
  cover property (DATA_IN == MAXPOS);                // max positive
  cover property (DATA_IN == NEG1);                  // -1

endmodule

// Example bind (connect your clock/reset):
// bind FxP_ABS_Function FxP_ABS_Function_sva #(.DATA_WIDTH(DATA_WIDTH))
//   u_abs_sva (.clk(tb_clk), .rst_n(tb_rst_n), .DATA_IN(DATA_IN), .DATA_ABS(DATA_ABS));