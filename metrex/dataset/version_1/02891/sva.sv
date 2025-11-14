// SVA for expand_message
// Bind this file alongside the DUT

module expand_message_sva (
  input logic        clk,
  input logic [55:0] rx_fixed_data,
  input logic [59:0] rx_nonce,
  input logic [511:0] tx_expanded_message
);

  // Track past-valid to safely use $past
  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Expected mapping (note: DUT RHS totals 418b -> zero-extended to 512b; pad 94 MSBs)
  function automatic logic [511:0] expected_expanded
    (input logic [55:0] fd, input logic [59:0] nc);
    expected_expanded = {
      94'h0,
      32'd192, 32'h0, 224'h0, 32'h80000000,
      fd[2], fd[1], fd[0], 8'h00, fd[6], fd[5], fd[4], fd[3],
      {4'b0,nc[2]}, {4'b0,nc[1]}, {4'b0,nc[0]}, 8'h00,
      {4'b0,nc[6]}, {4'b0,nc[5]}, {4'b0,nc[4]}, {4'b0,nc[3]},
      {4'b0,nc[10]}, {4'b0,nc[9]}, {4'b0,nc[8]}, {4'b0,nc[7]},
      {4'b0,nc[14]}, {4'b0,nc[13]}, {4'b0,nc[12]}, {4'b0,nc[11]}
    };
  endfunction

  // Functional equivalence (1-cycle registered)
  assert property (@(posedge clk) disable iff (!past_valid)
    tx_expanded_message == $past(expected_expanded(rx_fixed_data, rx_nonce)));

  // Structural sanity: zero-extended MSBs due to width mismatch (512-418 = 94)
  assert property (@(posedge clk) tx_expanded_message[511:418] == '0);

  // No X-propagation when inputs known
  assert property (@(posedge clk)
    !$isunknown({rx_fixed_data[6:0], rx_nonce[14:0]}) |-> !$isunknown(tx_expanded_message));

  // Coverage: exercise both edges on all used input bits
  genvar i;
  generate
    for (i=0; i<=6; i++) begin : cov_fd
      cover property (@(posedge clk) $rose(rx_fixed_data[i]));
      cover property (@(posedge clk) $fell(rx_fixed_data[i]));
    end
    for (i=0; i<=14; i++) begin : cov_nc
      cover property (@(posedge clk) $rose(rx_nonce[i]));
      cover property (@(posedge clk) $fell(rx_nonce[i]));
    end
  endgenerate

  // Coverage: observe any change on output (non-trivial activity)
  cover property (@(posedge clk) past_valid && tx_expanded_message != $past(tx_expanded_message));

endmodule

bind expand_message expand_message_sva sva_inst (.*);