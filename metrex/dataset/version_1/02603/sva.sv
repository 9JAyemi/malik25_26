// SVA checker for mux; bind it to the DUT and provide a sampling clock.
module mux_sva #(parameter int WIDTH = 1)
(
  input  logic                    clk,
  input  logic                    ctrl,
  input  logic [WIDTH-1:0]        D0,
  input  logic [WIDTH-1:0]        D1,
  input  logic [WIDTH-1:0]        S
);

  // Static sanity
  initial assert (WIDTH >= 1) else $error("mux WIDTH must be >= 1");

  // Functional equivalence: exact 4-state behavior (including default-to-0 on X/Z ctrl)
  assert property (@(posedge clk)
    S === ((ctrl===1'b1) ? D1 :
           (ctrl===1'b0) ? D0 : '0)
  ) else $error("mux func: S mismatch");

  // No X/Z on S when all driving inputs are known
  assert property (@(posedge clk)
    (!$isunknown(ctrl) && !$isunknown(D0) && !$isunknown(D1)) |-> !$isunknown(S)
  ) else $error("mux known-prop: S is X/Z with known inputs");

  // Basic functional coverage
  cover property (@(posedge clk) (ctrl===1'b0) && (S===D0));
  cover property (@(posedge clk) (ctrl===1'b1) && (S===D1));
  cover property (@(posedge clk) $isunknown(ctrl) && (S==='0));

  // Ensure we exercise discriminating cases where inputs differ
  cover property (@(posedge clk) (ctrl===1'b0) && (D0!==D1));
  cover property (@(posedge clk) (ctrl===1'b1) && (D0!==D1));

endmodule

// Bind example (provide a suitable clock from your environment)
// bind mux mux_sva #(.WIDTH(WIDTH)) u_mux_sva (.clk(tb_clk), .ctrl(ctrl), .D0(D0), .D1(D1), .S(S));