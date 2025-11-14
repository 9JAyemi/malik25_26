// SVA checker for decoder. Bind this to the DUT.
module decoder_sva #(parameter bit STRICT_XCHECK = 1) (
  input logic [2:0] in,
  input logic [7:0] out
);

  // Sample on any edge of any input bit (combinational sampling)
  default clocking cb @ (posedge in[0] or negedge in[0]
                       or posedge in[1] or negedge in[1]
                       or posedge in[2] or negedge in[2]); endclocking

  // Expected mapping: out == 8'h80 >> in (000 -> 1000_0000, 111 -> 0000_0001)
  // Guard against X/Z on inputs; optional strict X-check on outputs.
  property inputs_known; !$isunknown(in); endproperty

  // Functional equivalence
  a_decode_map: assert property ( inputs_known |-> (out == (8'h80 >> in)) )
    else $error("decoder: out=%b expected=%b for in=%b", out, (8'h80 >> in), in);

  // One-hot check
  a_onehot: assert property ( inputs_known |-> $onehot(out) )
    else $error("decoder: out not one-hot for in=%b, out=%b", in, out);

  // Output must be known when inputs are known (configurable)
  a_out_known: assert property ( (!STRICT_XCHECK || !inputs_known) or (!$isunknown(out)) )
    else $error("decoder: X/Z on out for known in=%b, out=%b", in, out);

  // Per-value decode coverage (full input space)
  c_in0: cover property ( inputs_known && (in==3'd0) && out==8'h80 );
  c_in1: cover property ( inputs_known && (in==3'd1) && out==8'h40 );
  c_in2: cover property ( inputs_known && (in==3'd2) && out==8'h20 );
  c_in3: cover property ( inputs_known && (in==3'd3) && out==8'h10 );
  c_in4: cover property ( inputs_known && (in==3'd4) && out==8'h08 );
  c_in5: cover property ( inputs_known && (in==3'd5) && out==8'h04 );
  c_in6: cover property ( inputs_known && (in==3'd6) && out==8'h02 );
  c_in7: cover property ( inputs_known && (in==3'd7) && out==8'h01 );

endmodule

// Bind into the DUT
bind decoder decoder_sva u_decoder_sva (.in(in), .out(out));