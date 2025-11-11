// SVA checker for int_to_float
// Concise, high-quality protocol + datapath checks and key covers

module int_to_float_sva (
  input  logic         clk,
  input  logic         rst,

  // DUT ports
  input  logic [31:0]  input_a,
  input  logic         input_a_stb,
  input  logic         output_z_ack,
  input  logic [31:0]  output_z,
  input  logic         output_z_stb,
  input  logic         input_a_ack,

  // DUT internals (bound)
  input  logic [2:0]   state,
  input  logic         s_input_a_ack,
  input  logic         s_output_z_stb,
  input  logic [31:0]  s_output_z,

  input  logic [31:0]  a, z, value,
  input  logic [23:0]  z_m,
  input  logic [7:0]   z_r,
  input  logic [7:0]   z_e,
  input  logic         z_s,
  input  logic         guard, round_bit, sticky
);

  // State encodings (mirror DUT)
  localparam get_a     = 3'd0;
  localparam convert_0 = 3'd1;
  localparam convert_1 = 3'd2;
  localparam convert_2 = 3'd3;
  localparam round_st  = 3'd4; // "round" is a keyword in some tools; map to round_st
  localparam pack      = 3'd5;
  localparam put_z     = 3'd6;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Basic sanity
  assert property (@(posedge clk) 1 |-> (state inside {get_a,convert_0,convert_1,convert_2,round_st,pack,put_z}))
    else $error("Illegal state");

  // Reset effects (checked during reset cycle)
  assert property (@(posedge clk) rst |-> (state==get_a && s_input_a_ack==0 && s_output_z_stb==0));

  // Handshake helpers
  sequence in_hs;  input_a_ack && input_a_stb; endsequence
  sequence out_hs; output_z_stb && output_z_ack; endsequence

  // Input side protocol
  assert property (input_a_ack |-> state==get_a);
  assert property (input_a_ack && !input_a_stb |=> input_a_ack); // ack sticks until handshake
  assert property (in_hs |=> state==convert_0 && !input_a_ack && a==$past(input_a));

  // Output side protocol
  assert property (output_z_stb |-> state==put_z);
  assert property (output_z_stb && !output_z_ack |=> output_z_stb); // strobe sticks until ack
  assert property (output_z_stb && !output_z_ack |=> $stable(output_z)); // data stable while waiting
  assert property (out_hs |=> state==get_a && !output_z_stb);

  // No simultaneous input-ack and output-stb
  assert property (!(input_a_ack && output_z_stb));

  // Liveness: accepted input eventually leads to output strobe (no reset)
  assert property (in_hs |-> ##[1:$] output_z_stb);

  // Datapath/algorithm checks

  // convert_0 (zero vs non-zero)
  assert property (state==convert_0 && a==0 |=> state==pack && z_s==0 && z_m==0);
  assert property (state==convert_0 && a!=0 |=> state==convert_1 &&
                   value==($past(a[31]) ? -$past(a) : $past(a)) &&
                   z_s==$past(a[31]));

  // convert_1 -> convert_2 setup
  assert property (state==convert_1 |=> state==convert_2 &&
                   z_e==8'd31 &&
                   z_m==$past(value[31:8]) &&
                   z_r==$past(value[7:0]));

  // convert_2 normalization loop step
  assert property (state==convert_2 && !z_m[23] |=> state==convert_2 &&
                   z_e==$past(z_e)-1 &&
                   z_m=={ $past(z_m[22:0]), $past(z_r[7]) } &&
                   z_r=={ $past(z_r[6:0]), 1'b0 });

  // convert_2 exit to round_st and GRS capture
  assert property (state==convert_2 && z_m[23] |=> state==round_st &&
                   guard==$past(z_r[7]) &&
                   round_bit==$past(z_r[6]) &&
                   sticky==($past(z_r[5:0])!=0));

  // round stage behavior
  assert property (state==round_st && (guard && (round_bit || sticky || z_m[0]))
                   |=> state==pack &&
                       z_m==$past(z_m)+1 &&
                       (($past(z_m)==24'hffffff) -> (z_e==$past(z_e)+1)));
  assert property (state==round_st && !(guard && (round_bit || sticky || z_m[0]))
                   |=> state==pack && z_m==$past(z_m) && z_e==$past(z_e));

  // pack -> put_z mapping
  assert property (state==pack |=> state==put_z &&
                   z[22:0]==$past(z_m[22:0]) &&
                   z[30:23]==$past(z_e)+8'd127 &&
                   z[31]==$past(z_s));

  // put_z drives output one cycle later
  assert property (state==put_z |=> output_z_stb && s_output_z==z);

  // Functional specials at output
  assert property (state==put_z |=> (a==0) -> (output_z==32'h0000_0000));
  assert property (state==put_z |=> (a!=0) -> (output_z[31]==a[31]));

  // No X on outputs when not in reset
  assert property (!rst |-> !$isunknown({input_a_ack, output_z_stb, output_z}));

  // Coverage

  // Full transaction: accept -> produce -> consume
  cover property (in_hs ##[1:$] output_z_stb ##[1:$] out_hs);

  // Zero input path reaches zero output
  cover property (in_hs && input_a==32'h0 ##[1:$] (output_z_stb && output_z==32'h0));

  // Normalization loop iterates at least once
  cover property (state==convert_2 && !z_m[23] ##1 state==convert_2 && z_m[23]);

  // Rounding increments mantissa (and possibly exponent)
  cover property (state==round_st && (guard && (round_bit || sticky || z_m[0])) ##1 state==pack);

endmodule

// Bind example (connect internals)
bind int_to_float int_to_float_sva sva_i (
  .clk(clk),
  .rst(rst),

  .input_a(input_a),
  .input_a_stb(input_a_stb),
  .output_z_ack(output_z_ack),
  .output_z(output_z),
  .output_z_stb(output_z_stb),
  .input_a_ack(input_a_ack),

  .state(state),
  .s_input_a_ack(s_input_a_ack),
  .s_output_z_stb(s_output_z_stb),
  .s_output_z(s_output_z),

  .a(a),
  .z(z),
  .value(value),
  .z_m(z_m),
  .z_r(z_r),
  .z_e(z_e),
  .z_s(z_s),
  .guard(guard),
  .round_bit(round_bit),
  .sticky(sticky)
);