// SVA for sqrt_pipelined
// Bind this module to the DUT instance to check/cover functionality
module sqrt_pipelined_sva #(
  parameter int INPUT_BITS = 16,
  localparam int OUTPUT_BITS = INPUT_BITS/2 + INPUT_BITS%2,
  localparam int L = OUTPUT_BITS-1,
  localparam int W = (2*(OUTPUT_BITS+1)) // wide enough to hold (root+1)^2
)(
  input  logic                           clk,
  input  logic                           reset_n,
  input  logic                           start,
  input  logic [INPUT_BITS-1:0]          radicand,
  input  logic                           data_valid,
  input  logic [OUTPUT_BITS-1:0]         root,

  // internal DUT signals (bound)
  input  logic [OUTPUT_BITS-1:0]         start_gen,
  input  logic [OUTPUT_BITS*INPUT_BITS-1:0] root_gen,
  input  logic [OUTPUT_BITS*INPUT_BITS-1:0] radicand_gen,
  input  logic [OUTPUT_BITS*INPUT_BITS-1:0] mask_gen
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n);

  // Helpers
  function automatic logic [W-1:0] zext_rad(input logic [INPUT_BITS-1:0] x);
    zext_rad = {{(W-INPUT_BITS){1'b0}}, x};
  endfunction

  function automatic logic [W-1:0] sqr_r(input logic [OUTPUT_BITS-1:0] x);
    logic [2*OUTPUT_BITS-1:0] tmp;
    tmp = x * x;
    sqr_r = {{(W-2*OUTPUT_BITS){1'b0}}, tmp};
  endfunction

  function automatic logic [W-1:0] sqr_rp1(input logic [OUTPUT_BITS-1:0] x);
    logic [OUTPUT_BITS:0] xp1;
    logic [2*(OUTPUT_BITS+1)-1:0] tmp;
    xp1 = {1'b0,x} + 1'b1;
    tmp = xp1 * xp1;
    sqr_rp1 = {{(W-2*(OUTPUT_BITS+1)){1'b0}}, tmp};
  endfunction

  // Reset state
  assert property ( !reset_n |-> (start_gen=='0 && radicand_gen=='0 && root_gen=='0 && data_valid==1'b0 && root=='0) );

  // Mask bus must be static (combinational constants)
  assert property ( $stable(mask_gen) );

  // Start pipeline propagation
  assert property ( start_gen[0] == $past(start) );
  genvar si;
  generate
    for (si=0; si<OUTPUT_BITS-1; si++) begin: a_start_pipe
      assert property ( start_gen[si+1] == $past(start_gen[si]) );
    end
  endgenerate

  // Per-stage datapath transfer checks
  genvar i;
  generate
    for (i=0; i<OUTPUT_BITS-1; i++) begin: a_stage
      // Aliases for readability
      wire [INPUT_BITS-1:0] root_i    = root_gen[INPUT_BITS*(i+1)-1 -: INPUT_BITS];
      wire [INPUT_BITS-1:0] rad_i     = radicand_gen[INPUT_BITS*(i+1)-1 -: INPUT_BITS];
      wire [INPUT_BITS-1:0] mask_next = mask_gen     [INPUT_BITS*(i+2)-1 -: INPUT_BITS];
      wire [INPUT_BITS-1:0] root_next = root_gen     [INPUT_BITS*(i+2)-1 -: INPUT_BITS];
      wire [INPUT_BITS-1:0] rad_next  = radicand_gen[INPUT_BITS*(i+2)-1 -: INPUT_BITS];

      // Take branch
      assert property (
        (root_i + mask_next <= rad_i)
        |=> ( rad_next  == $past(rad_i)  - $past(mask_next) - $past(root_i)
           && root_next == ($past(root_i) >> 1) + $past(mask_next) )
      );

      // No-take branch
      assert property (
        !(root_i + mask_next <= rad_i)
        |=> ( rad_next  == $past(rad_i)
           && root_next == ($past(root_i) >> 1) )
      );
    end
  endgenerate

  // Latency and bubble-free behavior
  assert property ( data_valid == $past(start, L) );
  assert property ( start |-> ##(L) data_valid );

  // Output mapping: root equals low OUTPUT_BITS of final slice
  wire [INPUT_BITS-1:0] final_slice = root_gen[OUTPUT_BITS*INPUT_BITS-1 -: INPUT_BITS];
  assert property ( root == final_slice[OUTPUT_BITS-1:0] );

  // Functional correctness of integer sqrt
  assert property (
    data_valid |-> ( sqr_r(root) <= zext_rad($past(radicand, L))
                  && zext_rad($past(radicand, L)) < sqr_rp1(root) )
  );

  // No X/Z on key signals after reset
  assert property ( !$isunknown({start,radicand,data_valid,root,start_gen,radicand_gen,root_gen,mask_gen}) );

  // Minimal, high-value coverage
  // Reset -> Start -> Valid
  cover property ( !reset_n ##1 reset_n ##1 start ##(L) data_valid );

  // First stage (entry) both branches exercised with start
  wire [INPUT_BITS-1:0] mask_entry = mask_gen[INPUT_BITS-1:0];
  cover property ( start && (radicand >= mask_entry) );
  cover property ( start && (radicand <  mask_entry) );

  // One pipeline branch taken and not-taken in early stage
  if (OUTPUT_BITS > 1) begin
    wire [INPUT_BITS-1:0] r0   = root_gen[INPUT_BITS*1-1 -: INPUT_BITS];
    wire [INPUT_BITS-1:0] rad0 = radicand_gen[INPUT_BITS*1-1 -: INPUT_BITS];
    wire [INPUT_BITS-1:0] m1   = mask_gen     [INPUT_BITS*2-1 -: INPUT_BITS];
    cover property ( r0 + m1 <= rad0 );
    cover property ( r0 + m1 >  rad0 );
  end

  // Back-to-back throughput
  cover property ( start ##1 start ##(L) data_valid ##1 data_valid );

  // Boundary inputs
  cover property ( start && (radicand == '0) );
  cover property ( start && (&radicand) );

endmodule

// Bind into DUT
bind sqrt_pipelined sqrt_pipelined_sva #(.INPUT_BITS(INPUT_BITS)) SVA (
  .clk(clk),
  .reset_n(reset_n),
  .start(start),
  .radicand(radicand),
  .data_valid(data_valid),
  .root(root),
  .start_gen(start_gen),
  .root_gen(root_gen),
  .radicand_gen(radicand_gen),
  .mask_gen(mask_gen)
);