
module top_module(
  input clk,
  input up_down,
  input load,
  input [2:0] D,
  // Corrected output order: MSB to LSB
  output [2:0] Q
  ,output wire Q2
  ,output wire Q1
  ,output wire Q0
);

  // Internal registers
  reg [2:0] counter_value;
  //reg [2:0] shift_register_value;

  // Instantiate sub-modules
  shift_register_3_bit shift_register(.A(D[2]), .load(load), .clk(clk), .Q2(Q2), .Q1(Q1), .Q0(Q0));
  up_down_counter counter(.clk(clk), .D(D), .up_down(up_down), .rst(1'b0), .Q(Q));

  // Combinational logic
  //assign shift_register_value = D;
  //assign counter_value = D;

  // Sequential logic
  always @(posedge clk) begin // Corrected block to handle register read-after-write
    if (load) begin
      counter_value <= D; //Corrected
    end else begin
      if (up_down) begin
        counter_value <= counter_value + 1;
      end else begin
        counter_value <= counter_value - 1;
      end
    end
  end
endmodule
module up_down_counter(
  input clk,
  input [2:0] D,
  input up_down,
  input rst,
  output [2:0] Q
);

  reg [2:0] Q_reg;

  // Sequential logic
  always @(posedge clk) begin
    if (rst) begin
      Q_reg <= 3'b0;
    end else begin
      if (up_down) begin
        Q_reg <= Q_reg + 1;
      end else begin
        Q_reg <= Q_reg - 1;
      end
    end
  end

  // Combinational logic
  assign Q = Q_reg;
endmodule
module shift_register_3_bit(
  input A,
  input load,
  input clk,
  output reg Q2,
  output reg Q1,
  output reg Q0
);

  // Sequential logic
  always @(posedge clk) begin
    if (load) begin
      Q2 <= A;
      Q1 <= A;
      Q0 <= A;
    end else begin
      Q2 <= Q1;
      Q1 <= Q0;
      Q0 <= A;
    end
  end

  // Combinational logic

endmodule