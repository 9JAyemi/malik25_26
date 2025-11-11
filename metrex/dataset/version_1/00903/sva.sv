// Add this SVA block inside the module (or guard with `ifdef ASSERT_ON)
`ifndef SYNTHESIS
// Default sampling clock for sequential checks
default clocking cb @(posedge clk); endclocking

// Elaboration-time sanity on parameters
initial begin
  assert (k==3 && n==4 && m==3)
    else $error("Param mismatch: expected k=3,n=4,m=3");
end

// Encoder: legal codewords only when MSB is 0
assert property ( !in[n-1] |-> (encoded inside {
  4'b0000,4'b1100,4'b1010,4'b0110,4'b1001,4'b0101,4'b0011,4'b1111
}) );

// Encoder: exact mapping for each 3-bit input when MSB is 0
assert property ( (!in[n-1] && in[2:0]==3'b000) |-> ##0 (encoded==4'b0000) );
assert property ( (!in[n-1] && in[2:0]==3'b001) |-> ##0 (encoded==4'b1100) );
assert property ( (!in[n-1] && in[2:0]==3'b010) |-> ##0 (encoded==4'b1010) );
assert property ( (!in[n-1] && in[2:0]==3'b011) |-> ##0 (encoded==4'b0110) );
assert property ( (!in[n-1] && in[2:0]==3'b100) |-> ##0 (encoded==4'b1001) );
assert property ( (!in[n-1] && in[2:0]==3'b101) |-> ##0 (encoded==4'b0101) );
assert property ( (!in[n-1] && in[2:0]==3'b110) |-> ##0 (encoded==4'b0011) );
assert property ( (!in[n-1] && in[2:0]==3'b111) |-> ##0 (encoded==4'b1111) );

// Encoder: when MSB is 1, combinational block should not change encoded
assert property ( (in[n-1] && $changed(in)) |-> $stable(encoded) );

// Encoder: encoded only changes in response to in changes
assert property ( $changed(encoded) |-> $changed(in) );

// Decoder: out equals lower m bits of in at the clock edge (blocking assign => same-cycle)
assert property ( @(posedge clk) out == in[m-1:0] );

// Decoder: out is directly driven by decoded
assert property ( out == decoded );

// Decoder: out only changes on clock rising edge
assert property ( $changed(out) |-> $rose(clk) );

// Decoder: no X/Z on out at clock edge
assert property ( @(posedge clk) !$isunknown(out) );

// Optional: flag potential data loss if upper input bits are used by testbench
// (Comment out if intentional)
// assert property ( in[n-1:m] == '0 );

// Coverage: hit all 3-bit encoder inputs (with MSB==0)
cover property ( !in[n-1] && in[2:0]==3'b000 );
cover property ( !in[n-1] && in[2:0]==3'b001 );
cover property ( !in[n-1] && in[2:0]==3'b010 );
cover property ( !in[n-1] && in[2:0]==3'b011 );
cover property ( !in[n-1] && in[2:0]==3'b100 );
cover property ( !in[n-1] && in[2:0]==3'b101 );
cover property ( !in[n-1] && in[2:0]==3'b110 );
cover property ( !in[n-1] && in[2:0]==3'b111 );

// Coverage: observe MSB==1 case (uncoded path / latent latch hazard)
cover property ( in[n-1] );

// Coverage: observe decoder updates
cover property ( @(posedge clk) $changed(out) );
`endif