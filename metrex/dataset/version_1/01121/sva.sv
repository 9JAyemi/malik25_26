// SVA checker for decoder
module decoder_sva (
  input  logic [3:0]  in,
  input  logic [15:0] out
);
  default clocking cb @(*) endclocking

  // Functional equivalence and shape check (no X when input known)
  property p_dec_func;
    !$isunknown(in) |-> ( out == ~(16'h1 << in) && $onehot(~out) && !$isunknown(out) );
  endproperty
  assert property (p_dec_func);

  // Corner values (optional explicit checks)
  assert property ( !$isunknown(in) |-> (in==4'd0  ->>  out==16'hFFFE) );
  assert property ( !$isunknown(in) |-> (in==4'd15 ->>  out==16'h7FFF) );

  // Coverage: hit every input code and corresponding output pattern
  genvar i;
  generate
    for (i=0; i<16; i++) begin : C_IN_VALS
      cover property ( (in==i) && (out == ~(16'h1 << i)) );
    end
  endgenerate

  // Coverage: every output bit observed low at least once (and uniquely low)
  generate
    for (i=0; i<16; i++) begin : C_OUT_BITS
      cover property ( !$isunknown(in) && (in==i) && (~out[i]) && $onehot(~out) );
    end
  endgenerate
endmodule

// Bind into DUT
bind decoder decoder_sva u_decoder_sva (.in(in), .out(out));