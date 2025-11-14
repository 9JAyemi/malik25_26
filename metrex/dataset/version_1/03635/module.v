
module reverse_parity (
  input [2:0] in_vec,
  output [3:0] out_vec,
  output even_parity
);

  assign out_vec = {in_vec[2], in_vec[1], in_vec[0], ~^in_vec};
  assign even_parity = (^in_vec);

endmodule

module shift_register (
  input clk,
  input reset,
  input load,
  input [2:0] load_data,
  output serial_out
);

  reg [2:0] reg_data;

  always @(posedge clk, posedge reset) begin
    if (reset) begin
      reg_data <= 3'b0;
    end else if (load) begin
      reg_data <= load_data;
    end else begin
      reg_data <= {reg_data[1:0], 1'b0};
    end
  end

  assign serial_out = reg_data[0];

endmodule

module top_module (
  input clk,
  input reset,
  input [3:0] in_vec,
  input select,
  input load,
  input [2:0] load_data,
  output [3:0] out_vec,
  output even_parity,
  output serial_out
);

  wire [3:0] reverse_out_vec;
  wire reverse_even_parity;
  wire shift_serial_out;

  reverse_parity reverse_parity_inst (
    .in_vec(in_vec[2:0]),
    .out_vec(reverse_out_vec),
    .even_parity(reverse_even_parity)
  );

  shift_register shift_register_inst (
    .clk(clk),
    .reset(reset),
    .load(load),
    .load_data(load_data),
    .serial_out(shift_serial_out)
  );

  assign out_vec = select ? reverse_out_vec : 4'b0;
  assign even_parity = select ? reverse_even_parity : (^in_vec);
  assign serial_out = select ? 1'b0 : shift_serial_out;

endmodule
