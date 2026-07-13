
module up_counter (
  input clk,
  input reset,
  output reg [7:0] count
);

  always @ (posedge clk) begin
    if (reset) begin
      count <= 8'b0;
    end else begin
      count <= count + 1'b1;
    end
  end

endmodule
module down_counter (
  input clk,
  input reset,
  output reg [7:0] count
);

  always @ (posedge clk) begin
    if (reset) begin
      count <= 8'b11111111;
    end else begin
      count <= count - 1'b1;
    end
  end

endmodule
module triangular_waveform (
  input clk,
  input reset,
  input select,
  output wire [7:0] waveform
);

  wire [7:0] up_count;
  wire [7:0] down_count;

  up_counter up_counter_inst (
    .clk(clk),
    .reset(reset),
    .count(up_count)
  );

  down_counter down_counter_inst (
    .clk(clk),
    .reset(reset),
    .count(down_count)
  );

  assign waveform = select ? down_count : up_count;

endmodule