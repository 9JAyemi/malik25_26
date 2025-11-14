// SVA checker for priority_encoder
// Bind or instantiate alongside the DUT and drive clk with any sampling clock.

module priority_encoder_sva #(
  parameter int WIDTH = 4,
  parameter bit LSB_HIGH_PRIORITY = 0
)(
  input  logic                           clk,
  input  logic [WIDTH-1:0]               input_unencoded,
  input  logic                           output_valid,
  input  logic [$clog2(WIDTH)-1:0]       output_encoded,
  input  logic [WIDTH-1:0]               output_unencoded
);

  // helpers
  function automatic int unsigned find_lsb(input logic [WIDTH-1:0] v);
    int i; for (i=0;i<WIDTH;i++) if (v[i]) return i; return 0;
  endfunction
  function automatic int unsigned find_msb(input logic [WIDTH-1:0] v);
    int i; for (i=WIDTH-1;i>=0;i--) if (v[i]) return i; return 0;
  endfunction
  function automatic logic [WIDTH-1:0] onehot_idx(input int unsigned idx);
    logic [WIDTH-1:0] r; r='0; if (idx<WIDTH) r[idx]=1'b1; return r;
  endfunction
  function automatic bit none_above(input logic [WIDTH-1:0] v, input int unsigned idx);
    int i; for (i=idx+1;i<WIDTH;i++) if (v[i]) return 0; return 1;
  endfunction
  function automatic bit none_below(input logic [WIDTH-1:0] v, input int unsigned idx);
    int i; for (i=0;i<idx;i++) if (v[i]) return 0; return 1;
  endfunction

  int unsigned exp_idx;
  always_comb exp_idx = LSB_HIGH_PRIORITY ? find_lsb(input_unencoded)
                                          : find_msb(input_unencoded);

  default clocking cb @(posedge clk); endclocking

  // Core correctness
  assert property (output_valid == (|input_unencoded));
  assert property ((|input_unencoded) |-> ##0 (output_encoded == exp_idx));
  assert property (output_valid |-> ##0 input_unencoded[output_encoded]);
  assert property (output_valid |-> ##0 (output_encoded < WIDTH));
  assert property ($onehot0(output_unencoded));
  assert property (output_valid |-> ##0 $onehot(output_unencoded));
  assert property (output_valid |-> ##0 (output_unencoded == onehot_idx(exp_idx)));
  assert property (output_valid |-> ##0 ((output_unencoded & ~input_unencoded) == '0));

  // Priority rule (no higher/lower 1s than the chosen one)
  assert property (output_valid |-> ##0
                   (LSB_HIGH_PRIORITY ? none_below(input_unencoded, output_encoded)
                                      : none_above(input_unencoded, output_encoded)));

  // Sanity on X/Z propagation
  assert property (!$isunknown(input_unencoded) |-> ##0
                   (!$isunknown(output_valid) && !$isunknown(output_encoded) && !$isunknown(output_unencoded)));

  // Coverage
  genvar k;
  generate
    for (k=0; k<WIDTH; k++) begin : g_cov_onehot
      cover property (input_unencoded == onehot_idx(k) &&
                      output_valid && output_encoded == k &&
                      output_unencoded == onehot_idx(k));
    end
  endgenerate
  cover property ((!|input_unencoded) && !output_valid);
  cover property (input_unencoded[0] && input_unencoded[WIDTH-1] &&
                  output_valid &&
                  output_encoded == (LSB_HIGH_PRIORITY ? 0 : (WIDTH-1)));

endmodule

// Example bind (provide a sampling clk from your environment):
// bind priority_encoder priority_encoder_sva #(.WIDTH(WIDTH), .LSB_HIGH_PRIORITY(LSB_HIGH_PRIORITY))
//   u_pe_sva (.* , .clk(testbench_clk));