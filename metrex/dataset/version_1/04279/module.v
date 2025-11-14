module shift_add (
  input clk,
  input reset,
  input shift_dir,
  input [3:0] data_in,
  output [3:0] data_out
);

  reg [7:0] shift_reg = 8'b00000000;

  wire [3:0] shift_reg_out;
  wire [3:0] adder_out;

  // Instantiate the shift register
  shift_register shift_reg_inst (
    .clk(clk),
    .reset(reset),
    .shift_dir(shift_dir),
    .data_in(data_in),
    .data_out(shift_reg_out)
  );

  // Instantiate the adder
  adder adder_inst (
    .a(shift_reg_out),
    .b(data_in),
    .sum(adder_out)
  );

  // Assign the output of the adder to the shift register input
  always @ (posedge clk) begin
    if (reset) begin
      shift_reg <= 8'b00000000;
    end else begin
      shift_reg <= {shift_dir, adder_out};
    end
  end

  // Assign the output of the shift register to the module output
  assign data_out = shift_reg_out;

endmodule

// Shift register module
module shift_register (
  input clk,
  input reset,
  input shift_dir,
  input [3:0] data_in,
  output [3:0] data_out
);

  reg [7:0] shift_reg = 8'b00000000;

  always @ (posedge clk) begin
    if (reset) begin
      shift_reg <= 8'b00000000;
    end else begin
      if (shift_dir) begin
        shift_reg <= {shift_reg[6:0], data_in};
      end else begin
        shift_reg <= {data_in, shift_reg[7:1]};
      end
    end
  end

  assign data_out = shift_reg[3:0];

endmodule

// Adder module
module adder (
  input [3:0] a,
  input [3:0] b,
  output [3:0] sum
);

  assign sum = a + b;

endmodule