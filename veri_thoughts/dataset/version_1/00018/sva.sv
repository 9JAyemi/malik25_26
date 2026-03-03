// SVA for mux_4to1: concise, high-quality checks and coverage
module mux_4to1_sva (
  input logic [3:0] in,
  input logic [1:0] sel,
  input logic       out
);

  // Combinational functional equivalence and X-behavior
  always_comb begin
    if (!$isunknown(sel)) begin
      assert (out === in[sel])
        else $error("mux_4to1: out != in[sel] (sel=%b in=%b out=%b)", sel, in, out);
    end else begin
      assert (out === 1'bx)
        else $error("mux_4to1: out not X when sel has X/Z (sel=%b out=%b)", sel, out);
    end

    // No spurious X on out when both sel and selected input are known
    assert (!$isunknown(out) || $isunknown(sel) || $isunknown(in[sel]))
      else $error("mux_4to1: out is X though sel and in[sel] are known (sel=%b in=%b out=%b)", sel, in, out);
  end

  // Coverage: each select exercised with both 0/1 data, and X-propagation when sel unknown
  generate
    for (genvar i = 0; i < 4; i++) begin : COV_PER_SEL
      localparam logic [1:0] IDX = i[1:0];
      cover property (@(*) ##0 (! $isunknown(sel) && sel == IDX && ! $isunknown(in[i]) && out === 1'b0));
      cover property (@(*) ##0 (! $isunknown(sel) && sel == IDX && ! $isunknown(in[i]) && out === 1'b1));
    end
  endgenerate

  cover property (@(*) ##0 ($isunknown(sel) && out === 1'bx));

endmodule

// Bind into the DUT
bind mux_4to1 mux_4to1_sva u_mux_4to1_sva (.in(in), .sel(sel), .out(out));