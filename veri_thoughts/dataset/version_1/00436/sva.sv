// SVA checker for Multiplexer_AC__parameterized69
// Bind example (provide tb clock/reset):
// bind Multiplexer_AC__parameterized69 mux_ac69_sva #(.WIDTH(WIDTH)) u_mux_chk ( .clk(tb_clk), .rst_n(tb_rst_n), .ctrl(ctrl), .D0(D0), .D1(D1), .S(S) );

module mux_ac69_sva #(parameter int WIDTH = 1)
(
  input  logic                 clk,
  input  logic                 rst_n,
  input  logic                 ctrl,
  input  logic [WIDTH-1:0]     D0,
  input  logic [WIDTH-1:0]     D1,
  input  logic [WIDTH-1:0]     S
);

  default clocking cb @(posedge clk); endclocking

  // Functional equivalence (4-state accurate, same-cycle)
  ap_func: assert property (disable iff (!rst_n)
    S === (ctrl ? D1 : D0)
  );

  // No unknowns on S when selection and selected input are known
  ap_no_x_sel0: assert property (disable iff (!rst_n)
    (ctrl === 1'b0 && !$isunknown(D0)) |-> (!$isunknown(S) && S == D0)
  );

  ap_no_x_sel1: assert property (disable iff (!rst_n)
    (ctrl === 1'b1 && !$isunknown(D1)) |-> (!$isunknown(S) && S == D1)
  );

  // X-propagation when ctrl is unknown and inputs differ
  ap_xprop_ctrl_x: assert property (disable iff (!rst_n)
    (ctrl !== 1'b0 && ctrl !== 1'b1 && (D0 !== D1)) |-> $isunknown(S)
  );

  // Stability: if inputs and ctrl are stable, S must be stable
  ap_stable: assert property (disable iff (!rst_n)
    $stable({ctrl, D0, D1}) |-> $stable(S)
  );

  // Coverage
  cp_sel0: cover property (disable iff (!rst_n)
    (ctrl === 1'b0 && (D0 !== D1) && S === D0)
  );

  cp_sel1: cover property (disable iff (!rst_n)
    (ctrl === 1'b1 && (D1 !== D0) && S === D1)
  );

  cp_xcase: cover property (disable iff (!rst_n)
    (ctrl !== 1'b0 && ctrl !== 1'b1 && (D0 !== D1) && $isunknown(S))
  );

endmodule