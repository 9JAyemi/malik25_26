// SVA checkers and binds for decoder_0, DEMUX, decoder_1.
// Provide clk and rst_n from your environment.

module decoder_sva #(parameter int k=3, parameter int N=(1<<k))
(
  input logic clk, rst_n,
  input logic [k-1:0] in,
  input logic [N-1:0] out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  function automatic logic [N-1:0] dec_val (input logic [k-1:0] sel);
    logic [N-1:0] t; t='0; t[sel]=1'b1; return t;
  endfunction

  // Exact decode and one-hot for known inputs
  assert property ( !$isunknown(in) |-> ##0 (out == dec_val(in)) );
  assert property ( !$isunknown(in) |-> $onehot(out) );

  // Unknown input -> default branch drives 0
  assert property ( $isunknown(in) |-> ##0 (out == '0) );

  // Coverage: all input codes plus unknown case
  genvar i;
  generate for (i=0; i<N; i++) begin : COV_DEC
    cover property ( (in==i) ##0 (out==dec_val(i)) );
  end endgenerate
  cover property ( $isunknown(in) ##0 (out=='0) );
endmodule


module demux_sva #(parameter int k=3, parameter int N=(1<<k))
(
  input logic clk, rst_n,
  input logic in,
  input logic [k-1:0] c,
  input logic [N-1:0] out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  function automatic logic [N-1:0] lane (input logic [k-1:0] sel);
    logic [N-1:0] t; t='0; t[sel]=1'b1; return t;
  endfunction

  // Spec: demux = in ? one-hot(c) : 0 (this will flag the RTL bug)
  assert property ( !$isunknown({in,c}) |-> ##0 (out == (in ? lane(c) : '0)) );

  // Control unknown -> default branch drives 0
  assert property ( $isunknown(c) |-> ##0 (out=='0) );

  // One-hot-or-zero at all times; in==0 forces all zeros
  assert property ( $onehot0(out) );
  assert property ( (in==1'b0) |-> ##0 (out=='0) );

  // Coverage
  genvar j;
  generate for (j=0; j<N; j++) begin : COV_DMUX
    cover property ( in && (c==j) ##0 (out==lane(j)) );
  end endgenerate
  cover property ( !in ##0 (out=='0) );
  cover property ( $isunknown(c) ##0 (out=='0) );
endmodule


// Bindings (use your env's clk and rst_n)
bind decoder_0 decoder_sva u_decoder_0_sva (.clk(clk), .rst_n(rst_n), .in(in), .out(out));
bind decoder_1 decoder_sva u_decoder_1_sva (.clk(clk), .rst_n(rst_n), .in(in), .out(out));
bind DEMUX      demux_sva   u_demux_sva     (.clk(clk), .rst_n(rst_n), .in(in), .c(c), .out(out));