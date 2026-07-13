module inverter (
  input wire in,
  output wire out
);
  assign out = ~in;
endmodule

module ring_oscillator (
  input wire in,
  output wire out
);

  wire stage1, stage2, stage3, stage4, stage5;

  // Instantiate the inverter stages
  inverter inv1 (.in(in), .out(stage1));
  inverter inv2 (.in(stage1), .out(stage2));
  inverter inv3 (.in(stage2), .out(stage3));
  inverter inv4 (.in(stage3), .out(stage4));
  inverter inv5 (.in(stage4), .out(stage5));

  // Connect the output signal to the last stage in the ring
  assign out = stage5;

endmodule