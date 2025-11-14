// SVA for long_to_double
// Bind these checkers to your DUT:
//   bind long_to_double long_to_double_chk();

`ifndef LONG_TO_DOUBLE_SVA
`define LONG_TO_DOUBLE_SVA

module long_to_double_chk();

  // We are bound into the DUT scope; can directly see its signals/params.
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Alias DUT state parameters for readability
  localparam [2:0] GET_A     = get_a;
  localparam [2:0] CONV_0    = convert_0;
  localparam [2:0] CONV_1    = convert_1;
  localparam [2:0] CONV_2    = convert_2;
  localparam [2:0] ROUND_S   = round;
  localparam [2:0] PACK_S    = pack;
  localparam [2:0] PUT_Z     = put_z;

  // Basic sanity
  assert property ( state inside {GET_A,CONV_0,CONV_1,CONV_2,ROUND_S,PACK_S,PUT_Z} );
  assert property ( !$isunknown({input_a_ack, output_z_stb}) );
  assert property ( output_z_stb |-> !$isunknown(output_z) );

  // Reset behavior (next cycle)
  assert property ( rst |=> state==GET_A && s_input_a_ack==0 && s_output_z_stb==0 );

  // Handshake exclusivity
  assert property ( (state!=GET_A) |-> !input_a_ack );
  assert property ( input_a_ack |-> state==GET_A );

  assert property ( (state!=PUT_Z) |-> !output_z_stb );
  assert property ( output_z_stb |-> state==PUT_Z );

  // Input side protocol
  // Accept when in GET_A and stb high
  assert property ( state==GET_A && input_a_stb |=> state==CONV_0 && s_input_a_ack==0 && a==$past(input_a) );
  // Otherwise hold in GET_A with ack high
  assert property ( state==GET_A && !input_a_stb |=> state==GET_A && input_a_ack );

  // 'a' only changes on input handshake
  assert property ( $changed(a) |-> $past(state==GET_A && input_a_stb) );

  // State progression
  assert property ( state==CONV_0 && a==64'd0 |=> state==PACK_S );
  assert property ( state==CONV_0 && a!=64'd0 |=> state==CONV_1 );
  assert property ( state==CONV_1 |=> state==CONV_2 );

  // Normalize loop and exit
  assert property ( state==CONV_2 && z_m[52]==1'b0 |=> state==CONV_2 );
  assert property ( state==CONV_2 && z_m[52]==1'b1 |=> state==ROUND_S );

  // Round then pack then put_z
  assert property ( state==ROUND_S |=> state==PACK_S );
  assert property ( state==PACK_S  |=> state==PUT_Z  );

  // Output side protocol and stability
  assert property ( state==PUT_Z && output_z_stb && !output_z_ack |=> state==PUT_Z && output_z_stb );
  assert property ( state==PUT_Z && output_z_stb && output_z_ack |=> state==GET_A && !output_z_stb );
  assert property ( output_z_stb && !output_z_ack |=> $stable(output_z) );
  // 'output_z' only updates when entering/being in PUT_Z
  assert property ( $changed(output_z) |-> $past(state==PUT_Z) );

  // Functional spot-checks
  // Zero input produces +0.0 exactly (fixed 3-cycle latency path: GET_A->CONV_0->PACK->PUT_Z)
  assert property ( (state==GET_A && input_a_stb && input_a==64'd0) |=> ##3 (output_z_stb && output_z==64'h0) );

  // Nonzero input sign propagates to output sign (latency variable; hold sampled sign)
  bit nz_sign;
  sequence accept_nz;
    (state==GET_A && input_a_stb && input_a!=64'd0, nz_sign = input_a[63]);
  endsequence
  assert property ( accept_nz |-> ##[1:$] (output_z_stb && output_z[63]==nz_sign) );

  // Exponent field never all-ones; for nonzero, exponent is in [1..1087]
  assert property ( output_z_stb |-> output_z[62:52] != 11'h7ff );
  assert property ( output_z_stb && output_z!=64'h0 |-> output_z[62:52] inside {[11'd1:11'd1087]} );

  // Coverage
  cover property ( state==GET_A && input_a_stb && input_a==64'd0 ##3 output_z_stb && output_z==64'h0 );
  cover property ( state==GET_A && input_a_stb && input_a[63]==1'b0 && input_a!=64'd0 ##[1:$] output_z_stb && output_z[63]==1'b0 );
  cover property ( state==GET_A && input_a_stb && input_a[63]==1'b1 && input_a!=64'd0 ##[1:$] output_z_stb && output_z[63]==1'b1 );
  // Normalize iterated at least once
  cover property ( state==CONV_2 && z_m[52]==0 ##1 state==CONV_2 && z_m[52]==1 );
  // Rounding that increments exponent (max carry case)
  cover property ( state==ROUND_S && guard && (round_bit || sticky || z_m[0]) && z_m==53'h1fffffffffffff ##1 state==PACK_S ##1 state==PUT_Z && output_z[62:52]==11'd1087 );
  // Output held until ack
  cover property ( state==PUT_Z && output_z_stb && !output_z_ack [*3] ##1 output_z_ack );

endmodule

`endif // LONG_TO_DOUBLE_SVA