
module binary_counter (
  input clk,
  input reset,
  output reg [3:0] count_out
);

  always @(posedge clk, posedge reset) begin
    if (reset) begin
      count_out <= 4'b0000;
    end else begin
      count_out <= count_out + 1;
    end
  end

endmodule
module parity_checker (
  input [7:0] data_in,
  output wire parity_out
);

  assign parity_out = ~^data_in;

endmodule
module top_module (
  input clk,
  input reset,
  output [3:0] counter_out,
  input [7:0] data_in,
  output wire parity_out,
  output [3:0] final_out
);

  binary_counter counter_inst (
    .clk(clk),
    .reset(reset),
    .count_out(counter_out)
  );

  parity_checker parity_inst (
    .data_in(data_in),
    .parity_out(parity_out)
  );

  assign final_out = counter_out + parity_out;

endmodule