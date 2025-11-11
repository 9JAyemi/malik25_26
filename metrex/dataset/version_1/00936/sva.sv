// SVA checker for hamming. Concise, focuses on key functionality and robustness.
// Bind into the DUT to gain access to internal wires (parity/syndrome/corrected).
`ifndef SYNTHESIS
module hamming_sva #(
  parameter int k = 4,
  parameter int n = 7
)(
  input  logic                     clk,
  input  logic                     rst_n,

  // DUT I/O
  input  logic [k-1:0]             data_in,
  input  logic [n-1:0]             received,
  input  logic [n-1:0]             encoded,
  input  logic [k-1:0]             data_out,

  // DUT internals (bound to internal nets)
  input  logic [n-k-1:0]           parity,
  input  logic [n-k-1:0]           syndrome,
  input  logic [n-1:0]             corrected
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Combinational equivalence and integrity (immediate) checks
  always_comb begin
    // Encoder concatenation and placement
    assert (encoded == {parity, data_in})
      else $error("encoded must be {parity,data_in}");
    assert (encoded[k-1:0] == data_in)
      else $error("encoded data field mismatch");

    // Decoder structure and non-intrusiveness to data field
    assert (corrected == (received ^ {syndrome, {k{1'b0}}}))
      else $error("corrected must be received ^ {syndrome,0}");
    assert (corrected[k-1:0] == received[k-1:0])
      else $error("decoder must not alter data field bits");
    assert (data_out == corrected[n-1:n-k])
      else $error("data_out must be MSB slice of corrected");

    // No X/Z propagation on known inputs
    if (!$isunknown({data_in, received})) begin
      assert (!$isunknown({encoded, data_out, parity, syndrome, corrected}))
        else $error("Unknown (X/Z) detected on outputs/internals");
    end
  end

  // No-error path: if received matches current encode, decoder must pass-through
  property p_no_error_pass;
    {parity, data_in} == received |-> (syndrome == '0 && corrected == received && data_out == data_in);
  endproperty
  assert property (p_no_error_pass);

  // Independence: encoder independent of 'received'; decoder independent of 'data_in'
  assert property ($changed(received) && !$changed(data_in) |-> ##0 $stable(encoded));
  assert property ($changed(data_in) && !$changed(received) |-> ##0 $stable(data_out));

  // Basic coverage
  cover property ({parity, data_in} == received);                 // no-error case observed
  cover property ($onehot(received ^ {parity, data_in}));         // single-bit error observed
  cover property (data_in == '0);                                 // all-zero data
  cover property (&data_in);                                      // all-ones data
  cover property ($onehot0(data_in));                             // onehot/zero data patterns

  // Per-bit single-error coverage across entire received vector
  genvar b;
  generate
    for (b = 0; b < n; b++) begin : C_ERR_BIT
      cover property (($onehot(received ^ {parity, data_in})) &&
                      ((received ^ {parity, data_in})[b]));
    end
  endgenerate

endmodule

// Example bind (connect a TB clock/reset and DUT internals/ports):
// bind hamming hamming_sva #(.k(k), .n(n)) u_hamming_sva (
//   .clk      (tb_clk),
//   .rst_n    (tb_rst_n),
//   .data_in  (data_in),
//   .received (received),
//   .encoded  (encoded),
//   .data_out (data_out),
//   .parity   (parity),
//   .syndrome (syndrome),
//   .corrected(corrected)
// );
`endif