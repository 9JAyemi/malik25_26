
module mux32_2 ( IN0, IN1, CTRL, OUT1 );
  input [31:0] IN0;
  input [31:0] IN1;
  output [31:0] OUT1;
  input CTRL;

  wire [0:0] mux_outs[31:0];

  // Instantiate 32 individual 2:1 multiplexers
  genvar i;
  generate
    for (i = 0; i < 32; i = i + 1) begin : mux_loop
      MUX2 U ( .A(IN0[i]), .B(IN1[i]), .S(CTRL), .Z(mux_outs[i]) );
    end
  endgenerate

  // Combine the outputs of the individual multiplexers to form the final output
  assign OUT1 = {mux_outs[31], mux_outs[30], mux_outs[29], mux_outs[28], mux_outs[27], mux_outs[26], mux_outs[25], mux_outs[24], mux_outs[23], mux_outs[22], mux_outs[21], mux_outs[20], mux_outs[19], mux_outs[18], mux_outs[17], mux_outs[16], mux_outs[15], mux_outs[14], mux_outs[13], mux_outs[12], mux_outs[11], mux_outs[10], mux_outs[9], mux_outs[8], mux_outs[7], mux_outs[6], mux_outs[5], mux_outs[4], mux_outs[3], mux_outs[2], mux_outs[1], mux_outs[0] };

endmodule
module MUX2 (A, B, S, Z);
  input A, B, S;
  output Z;

  assign Z = (S) ? B : A;

endmodule