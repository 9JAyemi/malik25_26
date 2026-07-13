module mux4to1(
  input in0,
  input in1,
  input in2,
  input in3,
  input sel0,
  input sel1,
  output reg out
);

  wire mux1_out, mux2_out;

  // First 2:1 MUX
  mux2to1 mux1 (
    .in0(in0),
    .in1(in1),
    .sel(sel0),
    .out(mux1_out)
  );

  // Second 2:1 MUX
  mux2to1 mux2 (
    .in0(in2),
    .in1(in3),
    .sel(sel0),
    .out(mux2_out)
  );

  // Final 2:1 MUX
  mux2to1 mux3 (
    .in0(mux1_out),
    .in1(mux2_out),
    .sel(sel1),
    .out(out)
  );

endmodule

// 2:1 MUX Implementation
module mux2to1(
  input in0,
  input in1,
  input sel,
  output reg out
);

  always @(*) begin
    if (sel == 1'b0) begin
      out = in0;
    end else begin
      out = in1;
    end
  end

endmodule