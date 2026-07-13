
module priority_encoder(
  input [3:0] in,  // number of input signals
  output [1:0] out
);

// assign out = $clog2(in);

// Synthesizable implementation of a priority encoder
assign out = (in[3] ? 2'b11 :
              (in[2] ? 2'b10 :
               (in[1] ? 2'b01 :
                (in[0] ? 2'b00 : 2'bxx))));

endmodule