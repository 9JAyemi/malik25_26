
module calculator (
  input clk,
  input areset, // async active-high reset to zero
  input load,
  input ena,
  input [2:0] bin_in,  // Binary input for the binary to binary converter
  input shift_left,   // Control input to shift left instead of right
  input operation,    // 0 for addition, 1 for subtraction
  output [3:0] result // 4-bit output from the shift register
);

  wire [2:0] bin_out;
  wire o2, o1, o0;
  binary_to_binary b2b(.vec(bin_in), .outv(bin_out), .o2(o2), .o1(o1), .o0(o0));
  shift_register sr(.clk(clk), .areset(areset), .load(load), .ena(ena), .shift_left(shift_left), .data_in({bin_out[2], bin_out[1], bin_out[0], o2, o1, o0}), .result(result));

  reg [3:0] reg_result;

  always @(posedge clk or posedge areset) begin
    if (areset) begin
      reg_result <= 0;
    end else if (load) begin
      reg_result <= {1'b0, bin_out};
    end else if (ena) begin
      if (operation == 0) begin
        reg_result <= reg_result + {1'b0, bin_out};
      end else begin
        reg_result <= reg_result - {1'b0, bin_out};
      end
    end
  end

endmodule
module binary_to_binary (
  input wire [2:0] vec, // 3-bit binary input
  output wire [2:0] outv, // Binary output
  output wire o2, // Output corresponding to the input binary at bit position 2
  output wire o1, // Output corresponding to the input binary at bit position 1
  output wire o0 // Output corresponding to the input binary at bit position 0
);

  assign outv = vec;
  assign o2 = vec[2];
  assign o1 = vec[1];
  assign o0 = vec[0];

endmodule
module shift_register (
  input clk,
  input areset, // async active-high reset to zero
  input load,
  input ena,
  input shift_left,   // Control input to shift left instead of right
  input [5:0] data_in, // 6-bit input for the shift register
  output reg [3:0] result // 4-bit output from the shift register
);

  always @(posedge clk or posedge areset) begin
    if (areset) begin
      result <= 0;
    end else if (load) begin
      result <= data_in[3:0];
    end else if (ena) begin
      if (shift_left) begin
        result <= {result[2:0], data_in[5]};
      end else begin
        result <= {data_in[4], result[3:1]};
      end
    end
  end

endmodule