// SVA checker for priority_encoder
// Focus: correctness of priority-encoding, internal transforms, and coverage.
// Bind this file to the DUT.

module priority_encoder_sva
(
  input  logic [7:0] in,
  input  logic [2:0] pos,
  input  logic [7:0] gray,
  input  logic [2:0] binary
);

  // Drive a sampling event on any input change; sample checks one delta later
  event pe_ev;
  always @(in) -> pe_ev;
  default clocking cb @ (pe_ev); endclocking

  // Helper: MSB index of an 8-bit vector (returns 0 if all zeros)
  function automatic logic [2:0] msb_idx8(logic [7:0] v);
    msb_idx8 = (v[7]) ? 3'd7 :
               (v[6]) ? 3'd6 :
               (v[5]) ? 3'd5 :
               (v[4]) ? 3'd4 :
               (v[3]) ? 3'd3 :
               (v[2]) ? 3'd2 :
               (v[1]) ? 3'd1 : 3'd0;
  endfunction

  // Basic X-prop/sanity
  assert property ( !$isunknown(in) |-> ##0 !$isunknown(pos) )
    else $error("priority_encoder: X/Z on input caused X/Z on pos or pos unknown");

  // Golden spec: pos must equal index of highest-order '1' in in (0 if all zero)
  assert property ( ##0 (pos == msb_idx8(in)) )
    else $error("priority_encoder: pos=%0d does not match MSB index of in=%b", pos, in);

  // White-box: internal transforms must match their stated equations (1-delta after input change)
  // gray generation
  assert property ( ##0 (gray[0] == in[0]) )
    else $error("gray[0] mismatch");
  genvar gi;
  generate
    for (gi=1; gi<8; gi++) begin : G
      assert property ( ##0 (gray[gi] == (in[gi-1] ^ in[gi])) )
        else $error("gray[%0d] mismatch", gi);
    end
  endgenerate

  // gray-to-binary generation (as coded)
  assert property ( ##0 (binary[2] == gray[7]) )
    else $error("binary[2] mismatch");
  assert property ( ##0 (binary[1] == (binary[2] ^ gray[6])) )
    else $error("binary[1] mismatch");
  assert property ( ##0 (binary[0] == (binary[1] ^ gray[5])) )
    else $error("binary[0] mismatch");

  // Priority on 'binary' driving pos (as coded)
  assert property ( ##0 ( binary[2] -> (pos==3) ) )
    else $error("pos mismatch when binary[2]=1");
  assert property ( ##0 ( (!binary[2] && binary[1]) -> (pos==2) ) )
    else $error("pos mismatch when binary[1]=1 and binary[2]=0");
  assert property ( ##0 ( (!binary[2] && !binary[1] && binary[0]) -> (pos==1) ) )
    else $error("pos mismatch when binary[0]=1 and higher zeros");
  assert property ( ##0 ( (!binary[2] && !binary[1] && !binary[0]) -> (pos==0) ) )
    else $error("pos mismatch when binary==0");

  // Coverage: hit each MSB choice (including all-zero)
  genvar k;
  generate
    for (k=0; k<8; k++) begin : C_MSB
      cover property ( ##0 (msb_idx8(in) == k && pos == k) );
    end
  endgenerate
  cover property ( ##0 (in==8'b0 && pos==3'd0) );

  // Coverage: observe each coded pos value
  cover property ( ##0 (pos==0) );
  cover property ( ##0 (pos==1) );
  cover property ( ##0 (pos==2) );
  cover property ( ##0 (pos==3) );

endmodule

// Bind into DUT (allows access to internal gray/binary)
bind priority_encoder priority_encoder_sva
(
  .in(in),
  .pos(pos),
  .gray(gray),
  .binary(binary)
);