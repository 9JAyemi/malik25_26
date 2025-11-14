
module parallel_load_shift (
  input clk,
  input reset,
  input [7:0] data_in,
  input [2:0] shift_amount,
  output reg [7:0] shift_out
);

  always @(posedge clk, posedge reset) begin
    if (reset) begin
      shift_out <= 8'b0;
    end else begin
      shift_out <= {shift_out[7-shift_amount:0], data_in};
    end
  end

endmodule
module combinational_circuit (
  input [49:0] in,
  output wire out_nand,
  output wire out_nor,
  output wire out_xnor
);

  assign out_nand = ~(&in);
  assign out_nor = ~(|in);
  assign out_xnor = ~(^in);

endmodule
module functional_module (
  input [7:0] shift_out,
  input [49:0] in,
  output reg [49:0] final_output
);

  always @(*) begin
    final_output = shift_out & in;
  end

endmodule
module top_module (
  input clk,
  input reset,
  input [7:0] data_in,
  input [2:0] shift_amount,
  input [49:0] in,
  input select,
  output [7:0] shift_out,
  output wire out_nand,
  output wire out_nor,
  output wire out_xnor,
  output reg [49:0] final_output
);

  wire [7:0] shift_out_wire;
  wire [49:0] in_wire;

  parallel_load_shift shift_module (
    .clk(clk),
    .reset(reset),
    .data_in(data_in),
    .shift_amount(shift_amount),
    .shift_out(shift_out_wire)
  );

  combinational_circuit comb_module (
    .in(in),
    .out_nand(out_nand),
    .out_nor(out_nor),
    .out_xnor(out_xnor)
  );

  functional_module func_module (
    .shift_out(shift_out_wire),
    .in(in_wire),
    .final_output(final_output)
  );

  assign in_wire = select ? 50'b0 : in;
  assign shift_out = shift_out_wire;

endmodule