// SVA for address_generator
// Focus: correctness vs. spec comment: addr = strand_offset + (strand_idx % strand_length)
// Also checks reset, X-propagation, corner cases, and covers key scenarios.

module address_generator_sva #(
  parameter int MEM_ADDR_WIDTH     = 24,
  parameter int STRAND_PARAM_WIDTH = 16
)(
  input  logic                         clk,
  input  logic                         rst_n,
  input  logic [STRAND_PARAM_WIDTH-1:0] strand_offset,
  input  logic [STRAND_PARAM_WIDTH-1:0] strand_idx,
  input  logic [STRAND_PARAM_WIDTH-1:0] strand_length,
  input  logic [MEM_ADDR_WIDTH-1:0]     addr
);

  // Zero-extend helper
  function automatic logic [MEM_ADDR_WIDTH-1:0] zext(input logic [STRAND_PARAM_WIDTH-1:0] x);
    zext = {{(MEM_ADDR_WIDTH-STRAND_PARAM_WIDTH){1'b0}}, x};
  endfunction

  // Expected address per spec (guard modulo-by-zero)
  function automatic logic [MEM_ADDR_WIDTH-1:0] exp_addr(
    input logic [STRAND_PARAM_WIDTH-1:0] off,
    input logic [STRAND_PARAM_WIDTH-1:0] idx,
    input logic [STRAND_PARAM_WIDTH-1:0] len
  );
    if (len == '0) exp_addr = 'x;
    else           exp_addr = zext(off) + zext(idx % len);
  endfunction

  // Reset behavior
  property p_reset_addr_zero;
    @(posedge clk) (!rst_n) |-> (addr == '0);
  endproperty
  assert property (p_reset_addr_zero);

  // Inputs must be known when in operation
  property p_no_x_inputs;
    @(posedge clk) disable iff (!rst_n) !$isunknown({strand_offset, strand_idx, strand_length});
  endproperty
  assert property (p_no_x_inputs);

  // strand_length must be non-zero in operation (modulo well-defined)
  property p_len_nonzero;
    @(posedge clk) disable iff (!rst_n) (strand_length != '0);
  endproperty
  assert property (p_len_nonzero);

  // Core functional check: addr matches spec (with proper width extension)
  property p_addr_matches_spec;
    @(posedge clk) disable iff (!rst_n)
      (strand_length != '0) |-> (addr == exp_addr(strand_offset, strand_idx, strand_length));
  endproperty
  assert property (p_addr_matches_spec);

  // Output must be known when inputs are known and length != 0
  property p_addr_known;
    @(posedge clk) disable iff (!rst_n)
      (strand_length != '0) && !$isunknown({strand_offset, strand_idx, strand_length}) |-> !$isunknown(addr);
  endproperty
  assert property (p_addr_known);

  // Coverage: reset seen
  cover property (@(posedge clk) !rst_n);
  // Coverage: idx < len path
  cover property (@(posedge clk) disable iff (!rst_n) (strand_length != '0) && (strand_idx < strand_length));
  // Coverage: boundary idx == len-1 and idx == len
  cover property (@(posedge clk) disable iff (!rst_n) (strand_length > 1) && (strand_idx == strand_length-1));
  cover property (@(posedge clk) disable iff (!rst_n) (strand_length != '0) && (strand_idx == strand_length));
  // Coverage: idx >= len path and >= 2*len (exercises correctness of true modulo vs. single subtract)
  cover property (@(posedge clk) disable iff (!rst_n) (strand_length != '0) && (strand_idx >= strand_length) && (strand_idx < (strand_length << 1)));
  cover property (@(posedge clk) disable iff (!rst_n) (strand_length != '0) && (strand_idx >= (strand_length << 1)));
  // Coverage: addition requires more than STRAND_PARAM_WIDTH bits (would expose 16-bit overflow if present)
  cover property (@(posedge clk) disable iff (!rst_n)
    (strand_length != '0) &&
    ( (zext(strand_offset) + zext(strand_idx % strand_length))[MEM_ADDR_WIDTH-1:STRAND_PARAM_WIDTH] != '0 )
  );

endmodule

// Bind into DUT; parameters inferred from DUT signal widths
bind address_generator address_generator_sva #(
  .MEM_ADDR_WIDTH($bits(addr)),
  .STRAND_PARAM_WIDTH($bits(strand_offset))
) i_address_generator_sva (
  .clk           (clk),
  .rst_n         (rst_n),
  .strand_offset (strand_offset),
  .strand_idx    (strand_idx),
  .strand_length (strand_length),
  .addr          (addr)
);