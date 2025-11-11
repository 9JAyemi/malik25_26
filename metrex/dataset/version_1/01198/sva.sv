// SVA for four_to_one_mux
// Bindable, concise, high-quality checks and coverage

module four_to_one_mux_sva #(
  parameter bit STRICT_NO_X = 0
)(
  input logic        clk,
  input logic        rst_n,
  input logic [3:0]  in,
  input logic [1:0]  sel,
  input logic        out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Functional equivalence: out must equal selected input when sel is known
  a_func: assert property ( !$isunknown(sel) |-> (out === in[sel]) );

  // If selection and selected input are known, out must be known
  a_known_out: assert property ( (!$isunknown(sel) && !$isunknown(in[sel])) |-> !$isunknown(out) );

  // Stability: if sel and selected input are stable, out must be stable
  a_stable: assert property ( $stable(sel) && $stable(in[sel]) |-> $stable(out) );

  // Optional strict checks (default off)
  if (STRICT_NO_X) begin
    a_sel_no_xz:  assert property ( !$isunknown(sel) );
    a_out_no_xz:  assert property ( !$isunknown(out) );
  end

  // Functional coverage: exercise each leg with both polarities
  genvar i;
  generate
    for (i=0; i<4; i++) begin : C
      c_sel_i_out0: cover property ( sel == i[1:0] && out == 1'b0 );
      c_sel_i_out1: cover property ( sel == i[1:0] && out == 1'b1 );
    end
  endgenerate

  // Coverage: walk through all selections in order
  c_walk: cover property ( sel==2'b00 ##1 sel==2'b01 ##1 sel==2'b10 ##1 sel==2'b11 );

endmodule

// Example bind (adjust clk/rst names as needed):
// bind four_to_one_mux four_to_one_mux_sva u_four_to_one_mux_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));