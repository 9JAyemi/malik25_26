// SVA checker for binary_search
// Bind this module to your DUT and drive clk/rst_n from your TB.

module binary_search_sva #(
  parameter int N       = 8,
  parameter int ELEM_W  = 2,
  parameter int IDX_W   = 3
)(
  input  logic                 clk,
  input  logic                 rst_n,
  input  logic [N*ELEM_W-1:0]  array,
  input  logic [ELEM_W-1:0]    search_key,
  input  logic [IDX_W-1:0]     index
);

  // Static design checks
  initial begin
    assert (N < (1<<IDX_W))
      else $error("binary_search: IDX_W(%0d) too small to encode invalid index N(%0d)", IDX_W, N);
    assert (ELEM_W == 2)
      else $error("binary_search: checker assumes 2-bit elements (ELEM_W==2)");
  end

  // Compute per-element comparisons
  logic [N-1:0] eq;
  for (genvar k = 0; k < N; k++) begin : g_eq
    assign eq[k] = (array[k*ELEM_W +: ELEM_W] == search_key);
  end
  logic [N-1:0] higher_match;
  for (genvar k2 = 0; k2 < N; k2++) begin : g_higher
    if (k2 == N-1) assign higher_match[k2] = 1'b0;
    else           assign higher_match[k2] = |eq[N-1:k2+1];
  end
  wire any_match = |eq;

  // Reference model: last (highest) matching index, or N (truncated to IDX_W)
  function automatic logic [IDX_W-1:0] ref_index(input logic [N*ELEM_W-1:0] arr,
                                                 input logic [ELEM_W-1:0]     key);
    logic [IDX_W-1:0] r;
    r = N[IDX_W-1:0];
    for (int i = 0; i < N; i++) begin
      if (arr[i*ELEM_W +: ELEM_W] == key) r = logic'(i[IDX_W-1:0]);
    end
    return r;
  endfunction

  // Functional equivalence (golden ref) — core check
  property p_func_equiv;
    @(posedge clk) disable iff (!rst_n)
      index == ref_index(array, search_key);
  endproperty
  assert property (p_func_equiv);

  // X-propagation hygiene: known inputs imply known output
  property p_no_unknown_out;
    @(posedge clk) disable iff (!rst_n)
      !($isunknown(array) || $isunknown(search_key)) |-> !$isunknown(index);
  endproperty
  assert property (p_no_unknown_out);

  // Optional: explicit no-match sentinel behavior (as implemented, N truncated to IDX_W)
  property p_no_match_sentinel;
    @(posedge clk) disable iff (!rst_n)
      !any_match |-> (index == N[IDX_W-1:0]);
  endproperty
  assert property (p_no_match_sentinel);

  // Coverage: no-match, each index hit, and multi-match picks highest
  cover property (@(posedge clk) disable iff (!rst_n) !any_match);
  for (genvar c = 0; c < N; c++) begin : g_cov_idx
    cover property (@(posedge clk) disable iff (!rst_n)
      eq[c] && !higher_match[c] && (index == c[IDX_W-1:0]));
  end
  cover property (@(posedge clk) disable iff (!rst_n)
    eq[0] && eq[N-1] && (index == (N-1)[IDX_W-1:0]));

endmodule

// Example bind (edit clk/rst_n to match your TB):
// bind binary_search binary_search_sva #(.N(8), .ELEM_W(2), .IDX_W(3))
//   u_bs_sva (.clk(tb_clk), .rst_n(tb_rst_n), .array(array), .search_key(search_key), .index(index));