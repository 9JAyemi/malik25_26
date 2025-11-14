module v89d234 #(
 parameter v422d28 = 0
) (
 input v41eb95,
 input [7:0] v39f831,
 input vf892a0,
 output [7:0] vb1c024
);
 localparam p0 = v422d28;
 wire [0:7] w1;
 wire [0:7] w2;
 wire w3;
 wire w4;
 assign vb1c024 = w1;
 assign w2 = v39f831;
 assign w3 = vf892a0;
 assign w4 = v41eb95;
 v89d234_v9148cb #(
  .INI(p0)
 ) v9148cb (
  .q(w1),
  .d(w2),
  .load(w3),
  .clk(w4)
 );
endmodule

module v89d234_v9148cb #(
 parameter INI = 0
) (
 output reg [7:0] q,
 input [7:0] d,
 input load,
 input clk
);
 always @(posedge clk) begin
  if (load) begin
   q <= d;
  end
 end
endmodule